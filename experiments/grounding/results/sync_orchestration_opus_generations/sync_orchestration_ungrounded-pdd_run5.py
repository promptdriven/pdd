"""
Orchestrates the complete PDD sync workflow by coordinating operations and
animations in parallel via a Textual-based TUI.

This module focuses solely on workflow orchestration, TUI coordination, and
operation execution using resolved paths provided by sync_main.
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
from dataclasses import dataclass, field

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

# TUI colour tokens
_GREEN = "green"
_YELLOW = "yellow"
_RED = "red"
_BLUE = "blue"


# ---------------------------------------------------------------------------
# AtomicStateUpdate
# ---------------------------------------------------------------------------
class AtomicStateUpdate:
    """Context manager that batches run-report and fingerprint writes.

    On successful exit both artefacts are written; on exception neither is
    persisted so the previous state remains intact.
    """

    def __init__(self, basename: str, language: str) -> None:
        self.basename = basename
        self.language = language
        self._pending_run_report: Optional[dict] = None
        self._pending_fingerprint: Optional[dict] = None

    # -- public setters used by callers inside the `with` block -------------

    def set_run_report(self, report_data: dict) -> None:
        self._pending_run_report = report_data

    def set_fingerprint(
        self, 
        operation: str, 
        paths: Dict[str, Path], 
        cost: float, 
        model: str,
    ) -> None:
        self._pending_fingerprint = {
            "operation": operation,
            "paths": paths,
            "cost": cost,
            "model": model,
        }

    # -- context-manager protocol -------------------------------------------

    def __enter__(self) -> "AtomicStateUpdate":
        return self

    def __exit__(self, exc_type, exc_val, exc_tb) -> bool:  # noqa: ANN001
        if exc_type is not None:
            return False
        self.commit()
        return False

    def commit(self) -> None:
        meta = META_DIR
        meta.mkdir(parents=True, exist_ok=True)
        safe = _safe_basename(self.basename)
        lang = self.language.lower()

        # Write run report via temp + rename
        if self._pending_run_report is not None:
            target = meta / f"{safe}_{lang}_run.json"
            _atomic_json_write(target, self._pending_run_report)

        # Write fingerprint via temp + rename
        if self._pending_fingerprint is not None:
            save_fingerprint(
                basename=self.basename,
                language=self.language,
                **self._pending_fingerprint,
            )


def _atomic_json_write(target: Path, data: dict) -> None:
    """Write *data* as JSON to *target* using a temp-file + rename."""
    target.parent.mkdir(parents=True, exist_ok=True)
    fd, tmp = tempfile.mkstemp(dir=str(target.parent), suffix=".tmp")
    try:
        with os.fdopen(fd, "w") as fh:
            json.dump(data, fh)
        os.replace(tmp, str(target))
    except BaseException:
        try:
            os.unlink(tmp)
        except OSError:
            pass
        raise


# ---------------------------------------------------------------------------
# Small helpers
# ---------------------------------------------------------------------------

def _use_agentic_path(language: str, agentic_mode: bool) -> bool:
    """Return *True* when the agentic (non-iterative) path should be used."""
    return language.lower() != "python" or agentic_mode


def _display_sync_log(basename: str, language: str, verbose: bool) -> List[dict]:
    """Load and pretty-print the sync log; return entries."""
    entries = load_operation_log(basename, language)
    if not entries:
        click.echo(f"No sync log entries for {basename} ({language}).")
        return entries
    for entry in entries:
        op = entry.get("operation", "?")
        ts = entry.get("timestamp", "")
        success = entry.get("success")
        cost = entry.get("actual_cost", entry.get("estimated_cost", 0))
        reason = entry.get("reason", "")
        if verbose:
            click.echo(
                f"  [{ts}] {op:15s}  success={success}  "
                f"cost=${cost:.4f}  type={entry.get('decision_type','') or ''}  "
                f"conf={entry.get('confidence','') or ''}  reason={reason}"
            )
        else:
            icon = "✓" if success else ("✗" if success is False else "·")
            click.echo(f"  {icon} {op:15s} ${cost:.4f}  {reason[:80]}")
    return entries


def _create_mock_context(
    command_name: str = "sync",
    strength: float = 0.5,
    temperature: float = 0.0,
    time_param: float = 0.25,
    verbose: bool = False,
    quiet: bool = False,
    force: bool = False,
    local: bool = False,
    context_override: Optional[str] = None,
    confirm_callback: Optional[Callable] = None,
    **extra: Any,
) -> click.Context:
    ctx = click.Context(click.Command(command_name))
    ctx.obj = {
        "strength": strength,
        "temperature": temperature,
        "time": time_param,
        "verbose": verbose,
        "quiet": quiet,
        "force": force,
        "local": local,
        "context": context_override,
        "confirm_callback": confirm_callback,
    }
    ctx.obj.update(extra)
    ctx.params = {"local": local, "force": force, "quiet": quiet}
    return ctx


# ---------------------------------------------------------------------------
# Test-output parsing
# ---------------------------------------------------------------------------

def _parse_test_output(output: str, language: str) -> tuple:
    """Return ``(tests_passed, tests_failed, coverage)`` from runner output."""
    passed = 0
    failed = 0
    coverage: Optional[float] = None
    lang = language.lower()

    if lang == "python":
        # pytest: "5 passed, 2 failed"
        m = re.search(r"(\d+)\s+passed", output)
        if m:
            passed = int(m.group(1))
        m = re.search(r"(\d+)\s+failed", output)
        if m:
            failed = int(m.group(1))
        # coverage: "TOTAL ... 90%"
        m = re.search(r"TOTAL\s+.*?(\d+)%", output)
        if m:
            coverage = float(m.group(1))
    elif lang in ("javascript", "typescript"):
        # Jest / Vitest / Mocha
        m = re.search(r"Tests:\s*(\d+)\s+passed", output)
        if m:
            passed = int(m.group(1))
        m = re.search(r"Tests:\s*\d+\s+passed,\s*(\d+)\s+failed", output)
        if m:
            failed = int(m.group(1))
        if not passed and not failed:
            m = re.search(r"(\d+)\s+passing", output)
            if m:
                passed = int(m.group(1))
            m = re.search(r"(\d+)\s+failing", output)
            if m:
                failed = int(m.group(1))
    elif lang == "go":
        passed = len(re.findall(r"^ok\s", output, re.MULTILINE))
        failed = len(re.findall(r"^FAIL\s", output, re.MULTILINE))
    elif lang == "rust":
        m = re.search(r"test result:.*?(\d+)\s+passed;\s*(\d+)\s+failed", output)
        if m:
            passed = int(m.group(1))
            failed = int(m.group(2))
    else:
        # generic fallback
        m = re.search(r"(\d+)\s+pass", output, re.IGNORECASE)
        if m:
            passed = int(m.group(1))
        m = re.search(r"(\d+)\s+fail", output, re.IGNORECASE)
        if m:
            failed = int(m.group(1))

    return passed, failed, coverage


def _python_cov_target_for_code_file(code_file: Optional[str]) -> Optional[str]:
    """Derive a ``--cov`` target from *code_file*."""
    if not code_file:
        return None
    p = Path(code_file)
    parts = list(p.with_suffix("").parts)
    # Strip leading 'src/' if present
    if parts and parts[0] == "src":
        parts = parts[1:]
    return ".".join(parts) if parts else None


def _python_cov_target_for_test_and_code(
    test_file: str, code_file: Optional[str], fallback: str
) -> str:
    """Pick the best ``--cov`` target by analysing test imports."""
    if code_file:
        cf = Path(code_file)
        # try to find a matching import in the test file
        try:
            test_src = Path(test_file).read_text(encoding="utf-8", errors="replace")
            stem = cf.stem
            for line in test_src.splitlines():
                if re.match(rf"^\s*(from|import)\s+{re.escape(stem)}\b", line):
                    return stem
        except OSError:
            pass
        target = _python_cov_target_for_code_file(code_file)
        if target:
            return target
    return fallback


# ---------------------------------------------------------------------------
# Example execution helpers
# ---------------------------------------------------------------------------

def _detect_example_errors(output: str) -> bool:
    """Return *True* if *output* contains Python tracebacks or ERROR markers."""
    if not output:
        return False
    patterns = [
        r"Traceback \(most recent call last\)",
        r"^\s*ERROR\s",
        r"ModuleNotFoundError:",
        r"ImportError:",
        r"SyntaxError:",
        r"NameError:",
        r"TypeError:",
        r"AttributeError:",
        r"FileNotFoundError:",
        r"ValueError:",
    ]
    combined = "|".join(f"(?:{p})" for p in patterns)
    return bool(re.search(combined, output, re.MULTILINE))


def _subprocess_env() -> dict:
    """Return a copy of ``os.environ`` without TUI-specific variables."""
    env = os.environ.copy()
    env.pop("FORCE_COLOR", None)
    env.pop("COLUMNS", None)
    return env


def _run_example_with_error_detection(
    example_path: str,
    code_path: str,
    language: str,
    timeout: int = 30,
) -> tuple:
    """Run *example_path* and return ``(returncode, stdout, stderr)``.

    For server-style examples that block, the *timeout* terminates them.
    Returns ``(None, stdout, stderr)`` on timeout.
    """
    lang = language.lower()
    env = _subprocess_env()

    if lang == "python":
        python_exe = detect_host_python_executable()
        cmd: List[str] = [python_exe, str(example_path)]
        project_root = _find_project_root(str(example_path))
        if project_root:
            pp = env.get("PYTHONPATH", "")
            additions = f"{project_root}{os.pathsep}{project_root}/src"
            env["PYTHONPATH"] = f"{additions}{os.pathsep}{pp}" if pp else additions
    else:
        cmd_str = get_run_command_for_file(str(example_path), language=language)
        if not cmd_str:
            return None, "", f"No run command found for {language}"
        cmd = cmd_str if isinstance(cmd_str, list) else cmd_str.split()
        project_root = None

    try:
        result = subprocess.run(
            cmd,
            capture_output=True,
            text=True,
            timeout=timeout,
            env=env,
            stdin=subprocess.DEVNULL,
            start_new_session=True,
            cwd=str(project_root) if project_root else None,
        )
        return result.returncode, result.stdout, result.stderr
    except subprocess.TimeoutExpired:
        return None, "", "Timeout – example may be a long-running server"
    except Exception as exc:
        return None, "", str(exc)


def _try_auto_fix_import_error(
    error_output: str, example_path: str, code_path: str
) -> bool:
    """Attempt lightweight auto-fix for common import errors.

    Returns *True* if the fix was applied (caller should re-run).
    """
    m = re.search(r"ModuleNotFoundError: No module named ['"](\w+)['"]", error_output)
    if not m:
        return False
    module_name = m.group(1)
    code_stem = Path(code_path).stem
    if module_name != code_stem:
        return False
    # Try injecting sys.path at the top of the example
    try:
        ex = Path(example_path)
        content = ex.read_text(encoding="utf-8")
        code_dir = str(Path(code_path).resolve().parent)
        fix_line = f"import sys; sys.path.insert(0, {code_dir!r})\n"
        if fix_line not in content:
            ex.write_text(fix_line + content, encoding="utf-8")
            return True
    except OSError:
        pass
    return False


# ---------------------------------------------------------------------------
# Test execution helpers
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
    """Run tests, parse output, create and persist a ``RunReport``."""
    lang = language.lower()
    env = _subprocess_env()
    all_test_files = list(test_files or [])
    if test_file and test_file not in all_test_files:
        all_test_files.insert(0, test_file)
    # de-duplicate while preserving order
    seen: set = set()
    unique_files: List[str] = []
    for tf in all_test_files:
        if tf not in seen and Path(tf).exists():
            seen.add(tf)
            unique_files.append(tf)
    all_test_files = unique_files

    if lang == "python":
        python_exe = detect_host_python_executable()
        first_test = all_test_files[0] if all_test_files else test_file
        project_root = _find_project_root(first_test)
        cmd: List[str] = [python_exe, "-m", "pytest", "-v"]
        if project_root:
            pp = env.get("PYTHONPATH", "")
            additions = f"{project_root}{os.pathsep}{project_root}/src"
            env["PYTHONPATH"] = f"{additions}{os.pathsep}{pp}" if pp else additions
            cmd.extend(["--rootdir", str(project_root), "-c", "/dev/null"])
        # coverage
        if code_file:
            cov_target = _python_cov_target_for_test_and_code(
                first_test, code_file, _safe_basename(basename)
            )
            cmd.extend(["--cov", cov_target, "--cov-report", "term-missing"])
            # also save xml for test_extend
            meta = META_DIR
            meta.mkdir(parents=True, exist_ok=True)
            cov_xml = meta / f"{_safe_basename(basename)}_{lang}_coverage.xml"
            cmd.extend(["--cov-report", f"xml:{cov_xml}"])
        cmd.extend(all_test_files)
    else:
        from .get_test_command import get_test_command_for_file as _gtcf

        raw_cmd = _gtcf(all_test_files[0] if all_test_files else test_file, language=language)
        if raw_cmd:
            cmd = raw_cmd if isinstance(raw_cmd, list) else raw_cmd.split()
        else:
            cmd = ["echo", "no test runner found"]

    try:
        result = subprocess.run(
            cmd,
            capture_output=True,
            text=True,
            timeout=300,
            env=env,
            stdin=subprocess.DEVNULL,
            start_new_session=True,
        )
        output = result.stdout + "\n" + result.stderr
        exit_code = result.returncode
    except subprocess.TimeoutExpired:
        output = "Test execution timed out after 300s"
        exit_code = 1
    except Exception as exc:
        output = str(exc)
        exit_code = 1

    passed, failed, coverage = _parse_test_output(output, language)
    if coverage is None:
        coverage = 0.0

    # Compute test file hashes
    test_hash = ""
    test_hashes: Dict[str, str] = {}
    for tf in all_test_files:
        try:
            h = calculate_sha256(Path(tf))
            test_hashes[tf] = h
            if tf == (all_test_files[0] if all_test_files else test_file):
                test_hash = h
        except OSError:
            pass

    report = RunReport(
        datetime.datetime.now().isoformat(),
        exit_code,
        passed,
        failed,
        coverage,
        test_hash=test_hash,
    )
    report_data = report.__dict__
    if test_hashes:
        report_data["test_file_hashes"] = test_hashes

    if atomic_state is not None:
        atomic_state.set_run_report(report_data)
    else:
        save_run_report(basename, language, report_data)

    return report


def _create_synthetic_run_report_for_agentic_success(
    test_file: str,
    basename: str,
    language: str,
    *,
    atomic_state: Optional[AtomicStateUpdate] = None,
) -> RunReport:
    """Create a synthetic successful run report after agentic test generation."""
    try:
        test_hash = calculate_sha256(Path(test_file)) if Path(test_file).exists() else "agentic_test_success"
    except OSError:
        test_hash = "agentic_test_success"

    report = RunReport(
        datetime.datetime.now().isoformat(),
        0,  # exit_code
        1,  # tests_passed
        0,  # tests_failed
        0.0,  # coverage unknown
        test_hash=test_hash,
    )
    report_data = report.__dict__

    if atomic_state is not None:
        atomic_state.set_run_report(report_data)
    else:
        save_run_report(basename, language, report_data)

    return report


# ---------------------------------------------------------------------------
# Cycle-detection helpers
# ---------------------------------------------------------------------------

def _detect_autodeps_cycle(history: List[str]) -> bool:
    last3 = history[-3:]
    return last3.count("auto-deps") >= 2


def _detect_alternation(history: List[str], op_a: str, op_b: str, max_repeats: int = 2) -> bool:
    """Detect an *op_a*/*op_b* alternation cycle in *history*."""
    pattern_len = max_repeats * 2
    if len(history) < pattern_len:
        return False
    tail = history[-pattern_len:]
    for i in range(0, len(tail), 2):
        if not ((tail[i] == op_a and i + 1 < len(tail) and tail[i + 1] == op_b) or
                (tail[i] == op_b and i + 1 < len(tail) and tail[i + 1] == op_a)):
            return False
    return True


def _count_consecutive_tail(history: List[str], op: str) -> int:
    count = 0
    for item in reversed(history):
        if item == op:
            count += 1
        else:
            break
    return count


# ---------------------------------------------------------------------------
# Headless detection
# ---------------------------------------------------------------------------

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


# ---------------------------------------------------------------------------
# get_confirm_callback factory
# ---------------------------------------------------------------------------

def _make_confirm_callback(
    force: bool,
    user_confirmed: List[bool],
    app_ref: Optional[List] = None,
) -> Callable[[str, str], bool]:
    """Return a confirm callback wired to the TUI or CLI."""

    def _callback(message: str, default: str = "y") -> bool:
        if force or user_confirmed[0]:
            return True
        if app_ref and app_ref[0] is not None:
            try:
                result = app_ref[0].request_confirmation(message)
            except Exception:
                result = True
        else:
            result = click.confirm(message, default=(default.lower() == "y"))
        if result:
            user_confirmed[0] = True
        return result

    return _callback


# ---------------------------------------------------------------------------
# File-colour update helper
# ---------------------------------------------------------------------------

def _set_color(ref: List[str], color: str) -> None:
    ref[0] = color


def _init_file_colors(
    pdd_files: dict,
    prompt_color: List, prompt_path: List,
    code_color: List, code_path: List,
    example_color: List, example_path: List,
    test_color: List, test_path: List,
) -> None:
    """Set initial TUI colours based on file existence."""
    for key, c_ref, p_ref in [
        ("prompt", prompt_color, prompt_path),
        ("code", code_color, code_path),
        ("example", example_color, example_path),
        ("test", test_color, test_path),
    ]:
        path = pdd_files.get(key)
        if path and Path(path).exists():
            c_ref[0] = _GREEN
        else:
            c_ref[0] = _RED
        p_ref[0] = str(path) if path else ""


# ---------------------------------------------------------------------------
# Main workflow logic
# ---------------------------------------------------------------------------

MAX_CYCLE_REPEATS = 2  # used inside sync_worker_logic


def sync_worker_logic(
    basename: str,
    language: str,
    ext: str,
    target_coverage: float,
    prompts_dir: str,
    code_dir: str,
    examples_dir: str,
    tests_dir: str,
    max_attempts: int,
    budget: float,
    skip_verify: bool,
    skip_tests: bool,
    force: bool,
    strength: float,
    temperature: float,
    time_param: float,
    verbose: bool,
    quiet: bool,
    output_cost: Optional[str],
    review_examples: bool,
    local: bool,
    context_config: Optional[Dict[str, str]],
    context_override: Optional[str],
    confirm_callback: Optional[Callable],
    no_steer: bool,
    steer_timeout: float,
    agentic_mode: bool,
    # TUI communication refs
    function_name_ref: List[str],
    cost_ref: List[float],
    prompt_color_ref: List[str],
    prompt_path_ref: List[str],
    code_color_ref: List[str],
    code_path_ref: List[str],
    example_color_ref: List[str],
    example_path_ref: List[str],
    test_color_ref: List[str],
    test_path_ref: List[str],
    stop_event: threading.Event,
    app_ref: List,
    progress_callback_ref: List,
) -> Dict[str, Any]:
    """Core sync workflow executed inside the TUI worker thread (or headless)."""

    start_time = time.monotonic()
    total_cost = 0.0
    operations_completed: List[str] = []
    skipped_operations: List[str] = []
    errors: List[str] = []
    last_model = ""
    op_history: List[str] = []
    test_extend_count = 0
    user_confirmed_overwrite = [False]

    if confirm_callback is None:
        confirm_callback = _make_confirm_callback(force, user_confirmed_overwrite, app_ref)

    def _ctx(cmd: str = "sync") -> click.Context:
        return _create_mock_context(
            command_name=cmd,
            strength=strength,
            temperature=temperature,
            time_param=time_param,
            verbose=verbose,
            quiet=quiet,
            force=force,
            local=local,
            context_override=context_override,
            confirm_callback=confirm_callback,
        )

    def _paths_dict(pf: dict) -> Dict[str, Path]:
        out: Dict[str, Path] = {}
        for k in ("prompt", "code", "example", "test"):
            v = pf.get(k)
            if v:
                out[k] = Path(v) if not isinstance(v, Path) else v
        return out

    # ---- Acquire lock & resolve paths ------------------------------------
    safe = _safe_basename(basename)
    lang = language.lower()

    try:
        lock = SyncLock(basename, language)
        lock.acquire()
    except Exception as exc:
        return {
            "success": False,
            "operations_completed": [],
            "skipped_operations": [],
            "total_cost": 0.0,
            "total_time": time.monotonic() - start_time,
            "final_state": {},
            "errors": [f"Lock acquisition failed: {exc}"],
            "error": str(exc),
            "model_name": "",
            "log_entries": [],
        }

    log_event(basename, language, "lock_acquired", {}, invocation_mode="sync")

    try:
        # Resolve file paths
        try:
            pdd_files = get_pdd_file_paths(
                basename, language,
                prompts_dir=prompts_dir,
                code_dir=code_dir,
                examples_dir=examples_dir,
                tests_dir=tests_dir,
            )
        except FileNotFoundError as fnf:
            if "test" in str(fnf).lower():
                # Construct defaults – tests will be generated later
                prompt_file = None
                # Case-insensitive lookup for the prompt
                pdir = Path(prompts_dir)
                if pdir.is_dir():
                    target = f"{basename}_{language}.prompt".lower()
                    for f in pdir.iterdir():
                        if f.name.lower() == target:
                            prompt_file = str(f)
                            break
                if not prompt_file:
                    prompt_file = str(pdir / f"{basename}_{language}.prompt")
                pdd_files = {
                    "prompt": prompt_file,
                    "code": str(Path(code_dir) / f"{basename}.{ext}"),
                    "example": str(Path(examples_dir) / f"{basename}_example.{ext}"),
                    "test": str(Path(tests_dir) / f"test_{basename}.{ext}"),
                }
            else:
                return {
                    "success": False,
                    "operations_completed": operations_completed,
                    "skipped_operations": skipped_operations,
                    "total_cost": total_cost,
                    "total_time": time.monotonic() - start_time,
                    "final_state": {},
                    "errors": [str(fnf)],
                    "error": str(fnf),
                    "model_name": last_model,
                    "log_entries": [],
                }

        prompt_path = str(pdd_files.get("prompt", ""))
        code_path = str(pdd_files.get("code", ""))
        example_path = str(pdd_files.get("example", ""))
        test_path = str(pdd_files.get("test", ""))
        extra_test_files: List[str] = [str(p) for p in pdd_files.get("test_files", [])]

        _init_file_colors(
            pdd_files,
            prompt_color_ref, prompt_path_ref,
            code_color_ref, code_path_ref,
            example_color_ref, example_path_ref,
            test_color_ref, test_path_ref,
        )

        # ---- Main loop ---------------------------------------------------
        iteration = 0
        max_iterations = 30  # absolute safety net

        while iteration < max_iterations:
            iteration += 1

            if stop_event.is_set():
                errors.append("Stopped by user")
                break

            # 1. Determine next operation
            function_name_ref[0] = "analyzing"
            decision: SyncDecision = sync_determine_operation(
                basename, language, target_coverage, log_mode=False,
            )
            operation = decision.operation
            reason = decision.reason

            # 2. Terminal states
            if operation in _TERMINAL_STATES:
                if operation == "all_synced":
                    function_name_ref[0] = "all_synced"
                elif operation == "error":
                    errors.append(reason)
                    function_name_ref[0] = "error"
                elif operation == "fail_and_request_manual_merge":
                    errors.append(f"Manual merge required: {reason}")
                    function_name_ref[0] = "manual_merge"
                break

            # 3. Interactive steering
            if not no_steer and not _is_headless(quiet):
                steered_op, should_abort = maybe_steer_operation(
                    operation, reason, app_ref, quiet,
                    skip_tests, skip_verify,
                    timeout_s=steer_timeout,
                )
                if should_abort:
                    errors.append("Aborted by user steering")
                    log_event(basename, language, "steering_abort", {}, invocation_mode="sync")
                    break
                if steered_op != operation:
                    log_event(
                        basename, language, "steering_override",
                        {"from": operation, "to": steered_op},
                        invocation_mode="sync",
                    )
                    operation = steered_op
                    decision = SyncDecision(
                        operation=steered_op,
                        reason=f"Steered from {decision.operation}: {reason}",
                        confidence=decision.confidence,
                        estimated_cost=decision.estimated_cost,
                        decision_type="steering",
                    )

            # 4. Skip handling
            if operation == "verify" and (skip_verify or skip_tests):
                skipped_operations.append("verify")
                entry = create_log_entry(
                    operation="verify", reason="skipped by user flag",
                    invocation_mode="sync", estimated_cost=0,
                    confidence=1.0, decision_type="skip",
                )
                entry = update_log_entry(entry, success=True, cost=0, model="", duration=0, error=None)
                append_log_entry(basename, language, entry)
                save_fingerprint(
                    basename, language, operation="skip:verify",
                    paths=_paths_dict(pdd_files), cost=0, model="",
                )
                op_history.append("verify")
                continue

            if operation in ("test", "test_extend", "fix") and skip_tests:
                skipped_operations.append(operation)
                entry = create_log_entry(
                    operation=operation, reason="skipped by --skip-tests",
                    invocation_mode="sync", estimated_cost=0,
                    confidence=1.0, decision_type="skip",
                )
                entry = update_log_entry(entry, success=True, cost=0, model="", duration=0, error=None)
                append_log_entry(basename, language, entry)
                save_fingerprint(
                    basename, language, operation=f"skip:{operation}",
                    paths=_paths_dict(pdd_files), cost=0, model="",
                )
                op_history.append(operation)
                continue

            if operation == "crash" and skip_tests:
                skipped_operations.append("crash")
                # Synthetic run report so loop doesn't re-request crash
                report = RunReport(
                    datetime.datetime.now().isoformat(), 0, 0, 0, 0.0,
                    test_hash="",
                )
                save_run_report(basename, language, report.__dict__)
                save_fingerprint(
                    basename, language, operation="skip:crash",
                    paths=_paths_dict(pdd_files), cost=0, model="",
                )
                op_history.append("crash")
                continue

            # 5. Cycle detection
            if _detect_autodeps_cycle(op_history):
                logger.warning("Auto-deps cycle detected; forcing generate")
                operation = "generate"

            if _detect_alternation(op_history, "crash", "verify", MAX_CYCLE_REPEATS):
                logger.warning("Crash-verify cycle detected; breaking")
                errors.append("Stuck in crash↔verify cycle")
                break

            if _detect_alternation(op_history, "test", "fix", MAX_CYCLE_REPEATS):
                logger.warning("Test-fix cycle detected; breaking")
                errors.append("Stuck in test↔fix cycle")
                break

            if _count_consecutive_tail(op_history, "fix") >= 5:
                logger.warning("5 consecutive fix attempts; breaking")
                errors.append("Fix iterations exhausted")
                break

            if _count_consecutive_tail(op_history, "test") >= MAX_CONSECUTIVE_TESTS:
                logger.warning("Max consecutive tests reached; breaking")
                errors.append("Test iterations exhausted")
                break

            if _count_consecutive_tail(op_history, "crash") >= MAX_CONSECUTIVE_CRASHES:
                logger.warning("Max consecutive crashes reached; breaking")
                errors.append("Crash iterations exhausted")
                break

            if operation == "test_extend":
                test_extend_count += 1
                if test_extend_count > MAX_TEST_EXTEND_ATTEMPTS:
                    logger.info("Accepting current coverage after %d test_extend attempts", test_extend_count - 1)
                    skipped_operations.append("test_extend")
                    op_history.append("test_extend")
                    continue

            # 6. Budget check
            if total_cost >= budget:
                log_event(basename, language, "budget_exhausted", {"total_cost": total_cost}, invocation_mode="sync")
                errors.append(f"Budget exhausted: ${total_cost:.2f} >= ${budget:.2f}")
                break

            remaining = budget - total_cost
            if remaining < budget * 0.2:
                log_event(basename, language, "budget_warning", {"remaining": remaining}, invocation_mode="sync")

            # 7. Create log entry
            entry = create_log_entry(
                operation=operation,
                reason=reason,
                invocation_mode="sync",
                estimated_cost=getattr(decision, "estimated_cost", 0),
                confidence=getattr(decision, "confidence", 0),
                decision_type=getattr(decision, "decision_type", ""),
            )

            # 8. Execute operation
            function_name_ref[0] = operation
            op_start = time.monotonic()
            op_cost = 0.0
            op_model = ""
            op_success = False
            op_error: Optional[str] = None

            try:
                # ========= auto-deps =========
                if operation == "auto-deps":
                    prompt_color_ref[0] = _YELLOW
                    ctx = _ctx("auto-deps")
                    # work on a temp copy so auto_deps_main's output goes back to prompt
                    result = auto_deps_main(
                        ctx=ctx,
                        prompt_file=prompt_path,
                        directory_path=f"{examples_dir}/**/*.{ext}",
                        auto_deps_csv_path=str(PDD_DIR / "project_dependencies.csv"),
                        output=prompt_path,
                        force_scan=False,
                    )
                    _mod_prompt, op_cost, op_model = result
                    op_success = True
                    prompt_color_ref[0] = _GREEN

                # ========= generate =========
                elif operation == "generate":
                    code_color_ref[0] = _YELLOW
                    ctx = _ctx("generate")
                    result = code_generator_main(
                        ctx=ctx,
                        prompt_file=prompt_path,
                        output=code_path,
                        original_prompt_file_path=None,
                        force_incremental_flag=False,
                    )
                    _code, _inc, op_cost, op_model = result
                    op_success = True
                    code_color_ref[0] = _GREEN
                    # Delete stale run report
                    clear_run_report(basename, language)

                # ========= example =========
                elif operation == "example":
                    example_color_ref[0] = _YELLOW
                    ctx = _ctx("example")
                    result = context_generator_main(
                        ctx=ctx,
                        prompt_file=prompt_path,
                        code_file=code_path,
                        output=example_path,
                    )
                    _ex_code, op_cost, op_model = result
                    op_success = True
                    example_color_ref[0] = _GREEN

                # ========= crash =========
                elif operation == "crash":
                    code_color_ref[0] = _YELLOW
                    example_color_ref[0] = _YELLOW
                    use_agentic = _use_agentic_path(language, agentic_mode)
                    crash_attempts = 0 if use_agentic else max_attempts

                    if lang == "python":
                        # Run example to capture crash output
                        rc, stdout, stderr = _run_example_with_error_detection(
                            example_path, code_path, language,
                        )
                        crash_output = stderr or stdout
                        if rc == 0 and not _detect_example_errors(stdout + stderr):
                            # No crash – maybe stale state
                            op_success = True
                            op_cost = 0.0
                            op_model = ""
                            code_color_ref[0] = _GREEN
                            example_color_ref[0] = _GREEN
                        else:
                            # Try lightweight fix first
                            if _try_auto_fix_import_error(crash_output, example_path, code_path):
                                rc2, _, stderr2 = _run_example_with_error_detection(
                                    example_path, code_path, language,
                                )
                                if rc2 == 0:
                                    op_success = True
                                    op_cost = 0.0
                                    code_color_ref[0] = _GREEN
                                    example_color_ref[0] = _GREEN

                            if not op_success:
                                # Write error to temp file
                                err_fd, err_path = tempfile.mkstemp(suffix=".log")
                                try:
                                    with os.fdopen(err_fd, "w") as fh:
                                        fh.write(crash_output)
                                    ctx = _ctx("crash")
                                    cr = crash_main(
                                        ctx=ctx,
                                        prompt_file=prompt_path,
                                        code_file=code_path,
                                        program_file=example_path,
                                        error_file=err_path,
                                        output=code_path,
                                        output_program=example_path,
                                        loop=crash_attempts > 0,
                                        strength=strength,
                                        temperature=temperature,
                                        budget=remaining,
                                    )
                                    cr_success, _fc, _fp, _ca, op_cost, op_model = cr
                                    op_success = cr_success
                                finally:
                                    try:
                                        os.unlink(err_path)
                                    except OSError:
                                        pass
                    else:
                        # Non-Python: delegate entirely to agentic crash handler
                        crash_log = f"Non-Python module {basename}.{ext} needs crash verification"
                        err_fd, err_path = tempfile.mkstemp(suffix=".log")
                        try:
                            with os.fdopen(err_fd, "w") as fh:
                                fh.write(crash_log)
                            ctx = _ctx("crash")
                            cr = crash_main(
                                ctx=ctx,
                                prompt_file=prompt_path,
                                code_file=code_path,
                                program_file=example_path,
                                error_file=err_path,
                                output=code_path,
                                output_program=example_path,
                                loop=False,
                                strength=strength,
                                temperature=temperature,
                                budget=remaining,
                            )
                            cr_success, _fc, _fp, _ca, op_cost, op_model = cr
                            op_success = cr_success
                        finally:
                            try:
                                os.unlink(err_path)
                            except OSError:
                                pass

                    # Post-crash validation
                    if op_success:
                        code_color_ref[0] = _GREEN
                        example_color_ref[0] = _GREEN
                        if lang == "python":
                            # Re-run example to verify fix
                            rc, stdout, stderr = _run_example_with_error_detection(
                                example_path, code_path, language,
                            )
                            report = RunReport(
                                datetime.datetime.now().isoformat(),
                                rc if rc is not None else 1,
                                1 if rc == 0 else 0,
                                0 if rc == 0 else 1,
                                0.0,
                            )
                            save_run_report(basename, language, report.__dict__)
                        else:
                            # Trust agentic result
                            report = RunReport(
                                datetime.datetime.now().isoformat(), 0, 1, 0, 0.0,
                            )
                            save_run_report(basename, language, report.__dict__)
                    else:
                        code_color_ref[0] = _RED

                # ========= verify =========
                elif operation == "verify":
                    code_color_ref[0] = _YELLOW
                    use_agentic = _use_agentic_path(language, agentic_mode)
                    ver_attempts = 0 if use_agentic else max_attempts
                    ctx = _ctx("verify")
                    result = fix_verification_main(
                        ctx=ctx,
                        prompt_file=prompt_path,
                        code_file=code_path,
                        program_file=example_path,
                        output_results=str(META_DIR / f"{safe}_{lang}_verify.log"),
                        output_code=code_path,
                        output_program=example_path,
                        loop=ver_attempts > 0,
                        verification_program=None,
                        max_attempts=ver_attempts if ver_attempts > 0 else 1,
                        budget=remaining,
                        agentic_fallback=True,
                    )
                    v_success, _fp, _fc, _va, op_cost, op_model = result
                    op_success = v_success
                    code_color_ref[0] = _GREEN if op_success else _RED

                # ========= test =========
                elif operation == "test":
                    test_color_ref[0] = _YELLOW
                    ctx = _ctx("test")
                    result = cmd_test_main(
                        ctx=ctx,
                        prompt_file=prompt_path,
                        code_file=code_path,
                        output=test_path,
                        language=language,
                        coverage_report=None,
                        existing_tests=None,
                        target_coverage=target_coverage,
                        merge=False,
                        strength=strength,
                        temperature=temperature,
                    )
                    _test_code, op_cost, op_model, agentic_success = (
                        result[0], result[1], result[2], result[3]
                    )
                    op_success = True

                    # Post-test: create run report
                    if agentic_success is True:
                        _create_synthetic_run_report_for_agentic_success(
                            test_path, basename, language,
                        )
                    else:
                        if Path(test_path).exists():
                            all_tf = [test_path] + [
                                tf for tf in extra_test_files if tf != test_path
                            ]
                            _execute_tests_and_create_run_report(
                                test_path, basename, language, target_coverage,
                                code_file=code_path, test_files=all_tf,
                            )
                    test_color_ref[0] = _GREEN

                # ========= test_extend =========
                elif operation == "test_extend":
                    # Skip for non-Python when agentic (unless python/typescript)
                    if _use_agentic_path(language, agentic_mode) and lang not in ("python", "typescript"):
                        skipped_operations.append("test_extend")
                        op_history.append("test_extend")
                        continue

                    test_color_ref[0] = _YELLOW
                    cov_xml = META_DIR / f"{safe}_{lang}_coverage.xml"
                    cov_path = str(cov_xml) if cov_xml.exists() else None
                    existing = [test_path] + [
                        tf for tf in extra_test_files if tf != test_path
                    ]
                    existing = [t for t in existing if Path(t).exists()]

                    ctx = _ctx("test")
                    result = cmd_test_main(
                        ctx=ctx,
                        prompt_file=prompt_path,
                        code_file=code_path,
                        output=test_path,
                        language=language,
                        coverage_report=cov_path,
                        existing_tests=existing or None,
                        target_coverage=target_coverage,
                        merge=True,
                        strength=strength,
                        temperature=temperature,
                    )
                    _test_code, op_cost, op_model, agentic_success = (
                        result[0], result[1], result[2], result[3]
                    )
                    op_success = True

                    # Post-test_extend: create run report
                    use_synthetic = (
                        agentic_success is True
                        and lang not in ("python", "typescript")
                    )
                    if use_synthetic:
                        _create_synthetic_run_report_for_agentic_success(
                            test_path, basename, language,
                        )
                    else:
                        if Path(test_path).exists():
                            all_tf = [test_path] + [
                                tf for tf in extra_test_files if tf != test_path
                            ]
                            _execute_tests_and_create_run_report(
                                test_path, basename, language, target_coverage,
                                code_file=code_path, test_files=all_tf,
                            )
                    test_color_ref[0] = _GREEN

                # ========= fix =========
                elif operation == "fix":
                    code_color_ref[0] = _YELLOW
                    test_color_ref[0] = _YELLOW
                    use_agentic = _use_agentic_path(language, agentic_mode)
                    fix_attempts = 0 if use_agentic else max_attempts

                    # Pre-fix: run tests to get error output
                    all_tf = [test_path] + [
                        tf for tf in extra_test_files if tf != test_path
                    ]
                    all_tf = [t for t in all_tf if Path(t).exists()]

                    fix_test_file = test_path
                    err_content = ""

                    if lang == "python" and all_tf:
                        first_test = all_tf[0]
                        project_root = _find_project_root(first_test)
                        env = _subprocess_env()
                        py = detect_host_python_executable()
                        pre_cmd: List[str] = [py, "-m", "pytest", "-v"]
                        if project_root:
                            pp = env.get("PYTHONPATH", "")
                            additions = f"{project_root}{os.pathsep}{project_root}/src"
                            env["PYTHONPATH"] = f"{additions}{os.pathsep}{pp}" if pp else additions
                            pre_cmd.extend(["--rootdir", str(project_root), "-c", "/dev/null"])
                        pre_cmd.extend(all_tf)
                        try:
                            pre = subprocess.run(
                                pre_cmd, capture_output=True, text=True,
                                timeout=120, env=env,
                                stdin=subprocess.DEVNULL, start_new_session=True,
                            )
                            err_content = pre.stdout + "\n" + pre.stderr
                        except Exception as e:
                            err_content = str(e)

                        # Identify failing test file
                        failing = extract_failing_files_from_output(err_content)
                        if failing:
                            fix_test_file = failing[0]

                    err_fd, err_path = tempfile.mkstemp(suffix=".log")
                    try:
                        with os.fdopen(err_fd, "w") as fh:
                            fh.write(err_content)

                        ctx = _ctx("fix")
                        fr = fix_main(
                            ctx=ctx,
                            prompt_file=prompt_path,
                            code_file=code_path,
                            unit_test_file=fix_test_file,
                            error_file=err_path,
                            output_test=fix_test_file,
                            output_code=code_path,
                            output_results=str(META_DIR / f"{safe}_{lang}_fix.log"),
                            loop=fix_attempts > 0,
                            verification_program=example_path if Path(example_path).exists() else None,
                            max_attempts=fix_attempts if fix_attempts > 0 else 1,
                            budget=remaining,
                            auto_submit=False,
                            agentic_fallback=True,
                            strength=None,
                            temperature=None,
                            test_files=all_tf if len(all_tf) > 1 else None,
                        )
                        f_success, _ft, _fcode, _fa, op_cost, op_model = fr
                        op_success = f_success
                    finally:
                        try:
                            os.unlink(err_path)
                        except OSError:
                            pass

                    # Post-fix: update run report
                    if op_success:
                        if lang == "python":
                            _execute_tests_and_create_run_report(
                                test_path, basename, language, target_coverage,
                                code_file=code_path, test_files=all_tf,
                            )
                        else:
                            # Trust agentic result
                            _create_synthetic_run_report_for_agentic_success(
                                test_path, basename, language,
                            )
                        code_color_ref[0] = _GREEN
                        test_color_ref[0] = _GREEN
                    else:
                        code_color_ref[0] = _RED

                # ========= update =========
                elif operation == "update":
                    prompt_color_ref[0] = _YELLOW
                    ctx = _ctx("update")
                    result = update_main(
                        ctx=ctx,
                        input_prompt_file=prompt_path,
                        modified_code_file=code_path,
                        input_code_file=None,
                        output=prompt_path,
                        use_git=True,
                        simple=False,
                    )
                    _upd_prompt, op_cost, op_model = result
                    op_success = True
                    prompt_color_ref[0] = _GREEN

                else:
                    logger.warning("Unknown operation: %s", operation)
                    errors.append(f"Unknown operation: {operation}")
                    break

            except Exception as exc:
                import traceback as tb

                op_success = False
                op_error = str(exc)
                errors.append(f"{operation}: {exc}")
                logger.exception("Operation %s failed", operation)
                if verbose:
                    tb.print_exc()

            # 9. Update log entry
            op_duration = time.monotonic() - op_start
            entry = update_log_entry(
                entry, success=op_success, cost=op_cost,
                model=op_model, duration=op_duration, error=op_error,
            )
            append_log_entry(basename, language, entry)

            # 10. Update totals & state
            total_cost += op_cost
            cost_ref[0] = total_cost
            if op_model:
                last_model = op_model
            operations_completed.append(operation)
            op_history.append(operation)

            # Save fingerprint on success
            if op_success:
                try:
                    save_fingerprint(
                        basename, language, operation=operation,
                        paths=_paths_dict(pdd_files), cost=op_cost, model=op_model,
                    )
                except Exception:
                    logger.debug("Fingerprint save failed for %s", operation, exc_info=True)

        # ---- End of main loop -----

    finally:
        try:
            lock.release()
            log_event(basename, language, "lock_released", {}, invocation_mode="sync")
        except Exception:
            logger.debug("Lock release failed", exc_info=True)

    stop_event.set()

    # Build final state
    final_state: Dict[str, Any] = {}
    for key in ("prompt", "code", "example", "test"):
        p = pdd_files.get(key)
        final_state[key] = {
            "exists": Path(p).exists() if p else False,
            "path": str(p) if p else "",
        }

    elapsed = time.monotonic() - start_time
    success = len(errors) == 0

    return {
        "success": success,
        "operations_completed": operations_completed,
        "skipped_operations": skipped_operations,
        "total_cost": total_cost,
        "total_time": elapsed,
        "final_state": final_state,
        "errors": errors,
        "error": "; ".join(errors) if errors else None,
        "model_name": last_model,
        "log_entries": [],
    }


# ---------------------------------------------------------------------------
# Public entry point
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
    """Orchestrate the complete PDD sync workflow for *basename*.

    Returns a result dictionary with keys ``success``, ``operations_completed``,
    ``skipped_operations``, ``total_cost``, ``total_time``, ``final_state``,
    ``errors``, ``error``, ``model_name``, and (when *dry_run*) ``log_entries``.
    """

    # -- Defence in depth: replace None with defaults ----------------------
    if target_coverage is None:
        target_coverage = 90.0
    if budget is None:
        budget = 10.0
    if max_attempts is None:
        max_attempts = 3

    # -- Resolve file extension for language -------------------------------
    from .get_extension import get_extension  # function-scope import

    ext = get_extension(language)

    # -- Dry-run: display sync log and return ------------------------------
    if dry_run:
        entries = _display_sync_log(basename, language, verbose)
        # Also run determine_operation for live analysis
        decision = sync_determine_operation(basename, language, target_coverage, log_mode=True)
        click.echo(f"\nRecommended operation: {decision.operation}")
        click.echo(f"Reason: {decision.reason}")
        if verbose:
            click.echo(f"Decision type: {getattr(decision, 'decision_type', '')}")
            click.echo(f"Confidence: {getattr(decision, 'confidence', '')}")
            click.echo(f"Estimated cost: ${getattr(decision, 'estimated_cost', 0):.4f}")
        return {
            "success": True,
            "operations_completed": [],
            "skipped_operations": [],
            "total_cost": 0.0,
            "total_time": 0.0,
            "final_state": {},
            "errors": [],
            "error": None,
            "model_name": "",
            "log_entries": [e for e in entries],
        }

    # -- Shared mutable state for TUI communication -----------------------
    function_name_ref: List[str] = ["initializing"]
    cost_ref: List[float] = [0.0]
    prompt_color_ref: List[str] = [_BLUE]
    prompt_path_ref: List[str] = [""]
    code_color_ref: List[str] = [_BLUE]
    code_path_ref: List[str] = [""]
    example_color_ref: List[str] = [_BLUE]
    example_path_ref: List[str] = [""]
    test_color_ref: List[str] = [_BLUE]
    test_path_ref: List[str] = [""]
    stop_event = threading.Event()
    app_ref: List = [None]
    progress_callback_ref: List = [None]
    worker_result: List[Optional[Dict[str, Any]]] = [None]

    # -- Common kwargs for sync_worker_logic ------------------------------
    worker_kwargs: Dict[str, Any] = dict(
        basename=basename,
        language=language,
        ext=ext,
        target_coverage=target_coverage,
        prompts_dir=prompts_dir,
        code_dir=code_dir,
        examples_dir=examples_dir,
        tests_dir=tests_dir,
        max_attempts=max_attempts,
        budget=budget,
        skip_verify=skip_verify,
        skip_tests=skip_tests,
        force=force,
        strength=strength,
        temperature=temperature,
        time_param=time_param,
        verbose=verbose,
        quiet=quiet,
        output_cost=output_cost,
        review_examples=review_examples,
        local=local,
        context_config=context_config,
        context_override=context_override,
        confirm_callback=confirm_callback,
        no_steer=no_steer,
        steer_timeout=steer_timeout,
        agentic_mode=agentic_mode,
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
        app_ref=app_ref,
        progress_callback_ref=progress_callback_ref,
    )

    # -- Headless mode (CI / no-TTY / quiet) ------------------------------
    if _is_headless(quiet):
        os.environ["PDD_FORCE"] = "1"
        result = sync_worker_logic(**worker_kwargs)
        return result

    # -- TUI mode ---------------------------------------------------------
    def _worker() -> None:
        try:
            worker_result[0] = sync_worker_logic(**worker_kwargs)
        except Exception as exc:
            worker_result[0] = {
                "success": False,
                "operations_completed": [],
                "skipped_operations": [],
                "total_cost": cost_ref[0],
                "total_time": 0.0,
                "final_state": {},
                "errors": [str(exc)],
                "error": str(exc),
                "model_name": "",
                "log_entries": [],
            }
            logger.exception("Worker thread crashed")
            stop_event.set()

    app = SyncApp(
        worker_func=_worker,
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
    app_ref[0] = app

    app.run()

    # Check for worker exceptions
    if hasattr(app, "worker_exception") and app.worker_exception is not None:
        print(f"Error in sync worker: {app.worker_exception}", file=sys.stderr)
        import traceback
        traceback.print_exception(
            type(app.worker_exception),
            app.worker_exception,
            app.worker_exception.__traceback__,
            file=sys.stderr,
        )

    if worker_result[0] is None:
        return {
            "success": False,
            "operations_completed": [],
            "skipped_operations": [],
            "total_cost": cost_ref[0],
            "total_time": 0.0,
            "final_state": {},
            "errors": ["Sync was interrupted"],
            "error": "Sync was interrupted",
            "model_name": "",
            "log_entries": [],
        }

    # Show exit animation
    if not quiet:
        try:
            from .sync_tui import show_exit_animation

            show_exit_animation(
                worker_result[0].get("success", False),
                worker_result[0].get("operations_completed", []),
                worker_result[0].get("total_cost", 0.0),
                worker_result[0].get("total_time", 0.0),
                worker_result[0].get("errors", []),
            )
        except Exception:
            logger.debug("Exit animation failed", exc_info=True)

    return worker_result[0]
"""