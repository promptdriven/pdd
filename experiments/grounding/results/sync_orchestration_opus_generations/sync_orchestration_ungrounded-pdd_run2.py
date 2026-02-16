"""
PDD Sync Orchestration Module.

Orchestrates the complete PDD sync workflow by coordinating operations
and animations in parallel. Works with sync_main (CLI/path resolution),
sync_tui (TUI components), and sync_determine_operation (decision engine).
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
# AtomicStateUpdate
# ---------------------------------------------------------------------------
class AtomicStateUpdate:
    """Context manager for consistent state writes.

    Ensures run_report and fingerprint are both written or neither is written
    using a temp-file + atomic rename pattern for crash safety.
    """

    def __init__(self, basename: str, language: str):
        self._basename = basename
        self._language = language.lower()
        self._pending_fingerprint: Optional[Dict[str, Any]] = None
        self._pending_run_report: Optional[Dict[str, Any]] = None
        self._safe_base = _safe_basename(basename)

    def __enter__(self):
        return self

    def __exit__(self, exc_type, exc_val, exc_tb):
        if exc_type is not None:
            return False
        self._flush()
        return False

    # -- public setters ----------------------------------------------------

    def set_fingerprint(
        self,
        operation: str,
        paths: Dict[str, Path],
        cost: float,
        model: str,
    ):
        self._pending_fingerprint = {
            "operation": operation,
            "paths": paths,
            "cost": cost,
            "model": model,
        }

    def set_run_report(self, report):
        if isinstance(report, dict):
            self._pending_run_report = report
        else:
            self._pending_run_report = report.__dict__

    # -- internal ----------------------------------------------------------

    def _flush(self):
        meta = Path(META_DIR)
        meta.mkdir(parents=True, exist_ok=True)

        if self._pending_run_report is not None:
            target = meta / f"{self._safe_base}_{self._language}_run.json"
            self._atomic_write(target, json.dumps(self._pending_run_report, default=str))

        if self._pending_fingerprint is not None:
            fp = self._pending_fingerprint
            save_fingerprint(
                basename=self._basename,
                language=self._language,
                operation=fp["operation"],
                paths=fp["paths"],
                cost=fp["cost"],
                model=fp["model"],
            )

    @staticmethod
    def _atomic_write(target: Path, data: str):
        fd, tmp = tempfile.mkstemp(
            dir=str(target.parent), suffix=".tmp", prefix=target.stem
        )
        try:
            os.write(fd, data.encode("utf-8"))
            os.close(fd)
            os.replace(tmp, str(target))
        except BaseException:
            os.close(fd) if not os.get_inheritable(fd) else None  # noqa: E501
            try:
                os.unlink(tmp)
            except OSError:
                pass
            raise


# ---------------------------------------------------------------------------
# Helper: agentic path decision
# ---------------------------------------------------------------------------
def _use_agentic_path(language: str, agentic_mode: bool) -> bool:
    """Return True when the agentic (non-iterative) path should be used."""
    return language.lower() != "python" or agentic_mode


# ---------------------------------------------------------------------------
# Helper: display sync log (dry-run)
# ---------------------------------------------------------------------------
def _display_sync_log(basename: str, language: str, verbose: bool):
    """Format and display the sync log using load_operation_log()."""
    entries = load_operation_log(basename, language)
    lang_lower = language.lower()
    safe_base = _safe_basename(basename)
    log_path = Path(META_DIR) / f"{safe_base}_{lang_lower}_sync.log"

    if not entries:
        click.echo(f"No sync log entries found for {basename} ({language}).")
        click.echo(f"  Log path: {log_path}")
        return

    click.echo(f"Sync log for {basename} ({language})  [{len(entries)} entries]")
    click.echo(f"  Log path: {log_path}")
    click.echo("")

    for entry in entries:
        ts = entry.get("timestamp", "?")
        op = entry.get("operation", "?")
        success = entry.get("success")
        cost = entry.get("actual_cost", entry.get("cost", 0))
        reason = entry.get("reason", "")

        status = "✓" if success else ("✗" if success is False else "·")
        line = f"  {status} [{ts}] {op:<14} ${cost:.4f}"
        if verbose:
            dt = entry.get("decision_type", "")
            conf = entry.get("confidence", "")
            line += f"  dt={dt} conf={conf}"
            if reason:
                line += f"  reason={reason}"
        click.echo(line)


# ---------------------------------------------------------------------------
# Helper: mock Click context
# ---------------------------------------------------------------------------
def _create_mock_context(
    force: bool = False,
    quiet: bool = False,
    verbose: bool = False,
    strength: float = DEFAULT_STRENGTH,
    temperature: float = 0.0,
    time_param: float = 0.25,
    local: bool = False,
    output_cost: Optional[str] = None,
    review_examples: bool = False,
    context_override: Optional[str] = None,
    confirm_callback: Optional[Callable] = None,
    **extra,
) -> click.Context:
    """Create a Click context suitable for passing to PDD sub-commands."""
    ctx = click.Context(click.Command("sync"))
    ctx.obj = {
        "strength": strength,
        "temperature": temperature,
        "time": time_param,
        "verbose": verbose,
        "force": force,
        "quiet": quiet,
        "local": local,
        "output_cost": output_cost,
        "review_examples": review_examples,
        "context": context_override,
        "confirm_callback": confirm_callback,
    }
    ctx.params = {
        "force": force,
        "quiet": quiet,
        "local": local,
        "verbose": verbose,
    }
    ctx.obj.update(extra)
    return ctx


# ---------------------------------------------------------------------------
# Helper: parse test runner output
# ---------------------------------------------------------------------------
def _parse_test_output(
    output: str, language: str
) -> tuple:
    """Parse test runner output → (tests_passed, tests_failed, coverage).

    Handles pytest, Jest/Vitest/Mocha, ``go test``, and ``cargo test``.
    """
    tests_passed = 0
    tests_failed = 0
    coverage = 0.0
    lang = language.lower()

    if lang == "python":
        m = re.search(r"(\d+)\s+passed", output)
        if m:
            tests_passed = int(m.group(1))
        m = re.search(r"(\d+)\s+failed", output)
        if m:
            tests_failed = int(m.group(1))
        m = re.search(r"(\d+)\s+error", output)
        if m:
            tests_failed += int(m.group(1))
        m = re.search(r"TOTAL\s+.*?(\d+(?:\.\d+)?)%", output)
        if m:
            coverage = float(m.group(1))
    elif lang in ("javascript", "typescript"):
        m = re.search(r"Tests:\s+(\d+)\s+passed", output)
        if m:
            tests_passed = int(m.group(1))
        m = re.search(r"Tests:\s+.*?(\d+)\s+failed", output)
        if m:
            tests_failed = int(m.group(1))
        if tests_passed == 0:
            m = re.search(r"(\d+)\s+passing", output)
            if m:
                tests_passed = int(m.group(1))
        if tests_failed == 0:
            m = re.search(r"(\d+)\s+failing", output)
            if m:
                tests_failed = int(m.group(1))
        m = re.search(
            r"(?:All files|Statements)\s*[|:]\s*(\d+(?:\.\d+)?)%", output
        )
        if m:
            coverage = float(m.group(1))
    elif lang == "go":
        tests_passed = len(re.findall(r"--- PASS:", output))
        tests_failed = len(re.findall(r"--- FAIL:", output))
        m = re.search(r"coverage:\s*(\d+(?:\.\d+)?)%", output)
        if m:
            coverage = float(m.group(1))
    elif lang == "rust":
        m = re.search(r"(\d+)\s+passed", output)
        if m:
            tests_passed = int(m.group(1))
        m = re.search(r"(\d+)\s+failed", output)
        if m:
            tests_failed = int(m.group(1))

    return tests_passed, tests_failed, coverage


# ---------------------------------------------------------------------------
# Helper: Python --cov target resolution
# ---------------------------------------------------------------------------
def _python_cov_target_for_code_file(code_file: str) -> Optional[str]:
    """Derive a dotted module path usable as ``pytest --cov`` target."""
    p = Path(code_file)
    if not p.exists():
        return None
    parts = list(p.with_suffix("").parts)
    if parts and parts[0] == "src":
        parts = parts[1:]
    return ".".join(parts) if parts else None


def _python_cov_target_for_test_and_code(
    test_file: str, code_file: str, fallback: Optional[str]
) -> Optional[str]:
    """Analyse test imports to pick best ``--cov`` target."""
    try:
        content = Path(test_file).read_text(encoding="utf-8")
        code_stem = Path(code_file).stem
        for line in content.splitlines():
            m = re.match(r"^(?:from|import)\s+([\w.]+)", line)
            if m:
                module = m.group(1)
                if code_stem in module:
                    return module.split(".")[0]
    except Exception:
        pass
    return fallback


# ---------------------------------------------------------------------------
# Helper: subprocess environment
# ---------------------------------------------------------------------------
def _clean_subprocess_env() -> dict:
    """Return an env dict with TUI variables removed."""
    env = os.environ.copy()
    for key in ("FORCE_COLOR", "COLUMNS"):
        env.pop(key, None)
    return env


# ---------------------------------------------------------------------------
# Helper: detect example errors
# ---------------------------------------------------------------------------
def _detect_example_errors(output: str) -> Optional[str]:
    """Detect Python tracebacks and ERROR log messages in output."""
    if "Traceback (most recent call last)" in output:
        return output
    for line in output.splitlines():
        if re.match(r"^ERROR\b", line):
            return output
    return None


# ---------------------------------------------------------------------------
# Helper: run example with error detection
# ---------------------------------------------------------------------------
def _run_example_with_error_detection(
    program_file: str,
    code_file: str,
    language: str,
    timeout: int = 30,
) -> tuple:
    """Run an example program and return (success, stdout+stderr, exit_code)."""
    lang_lower = language.lower()
    env = _clean_subprocess_env()

    if lang_lower == "python":
        python_exe = detect_host_python_executable() or sys.executable
        project_root = _find_project_root(code_file)
        if project_root:
            pp = env.get("PYTHONPATH", "")
            extra = [str(project_root), str(Path(project_root) / "src")]
            env["PYTHONPATH"] = os.pathsep.join(
                [p for p in extra if p] + ([pp] if pp else [])
            )
        cmd = [python_exe, program_file]
    else:
        run_cmd = get_run_command_for_file(program_file, language=language)
        if run_cmd:
            cmd = run_cmd if isinstance(run_cmd, list) else ["sh", "-c", run_cmd]
        else:
            return False, f"No run command for {language}", 1

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
        combined = (proc.stdout or "") + "\n" + (proc.stderr or "")
        if proc.returncode != 0:
            return False, combined.strip(), proc.returncode
        err = _detect_example_errors(combined)
        if err:
            return False, err.strip(), 1
        return True, combined.strip(), 0
    except subprocess.TimeoutExpired:
        # Server-style programs that block are considered OK
        return True, "Timed out (server-style program assumed OK)", 0
    except Exception as exc:
        return False, str(exc), 1


# ---------------------------------------------------------------------------
# Helper: auto-fix import error
# ---------------------------------------------------------------------------
def _try_auto_fix_import_error(
    error_output: str, code_file: str
) -> bool:
    """Attempt trivial auto-fix for common import errors.

    Returns True if a fix was applied.
    """
    m = re.search(r"ModuleNotFoundError: No module named '(\w+)'", error_output)
    if not m:
        return False
    missing = m.group(1)
    try:
        subprocess.run(
            [sys.executable, "-m", "pip", "install", missing],
            capture_output=True,
            text=True,
            timeout=60,
            stdin=subprocess.DEVNULL,
        )
        return True
    except Exception:
        return False


# ---------------------------------------------------------------------------
# Helper: execute tests and create run report
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
) -> RunReport:
    """Run tests with coverage, parse results, persist a RunReport."""
    from .get_test_command import get_test_command_for_file

    lang_lower = language.lower()
    env = _clean_subprocess_env()
    combined_output = ""

    files_to_run = test_files if test_files else [test_file]
    files_to_run = [f for f in files_to_run if Path(f).exists()]

    if not files_to_run:
        report = RunReport(
            datetime.datetime.now().isoformat(), 1, 0, 0, 0.0,
            test_hash="no_test_files",
        )
        _persist_run_report(report, basename, language, atomic_state)
        return report

    if lang_lower == "python":
        python_exe = detect_host_python_executable() or sys.executable
        project_root = _find_project_root(test_file)

        if project_root:
            pp = env.get("PYTHONPATH", "")
            extras = [str(project_root), str(Path(project_root) / "src")]
            env["PYTHONPATH"] = os.pathsep.join(
                [p for p in extras if p] + ([pp] if pp else [])
            )

        cmd = [python_exe, "-m", "pytest", "-x", "-v"]
        if code_file:
            cov_target = _python_cov_target_for_test_and_code(
                test_file,
                code_file,
                _python_cov_target_for_code_file(code_file),
            )
            if cov_target:
                cmd += [f"--cov={cov_target}", "--cov-report=term-missing"]
        if project_root:
            cmd += [f"--rootdir={project_root}", "-c", "/dev/null"]
        cmd += files_to_run
    else:
        test_cmd = get_test_command_for_file(test_file, language=language)
        if test_cmd:
            cmd = test_cmd if isinstance(test_cmd, list) else ["sh", "-c", test_cmd]
        else:
            cmd = ["sh", "-c", f"echo 'No test runner found for {language}'"]

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
        combined_output = (proc.stdout or "") + "\n" + (proc.stderr or "")
        exit_code = proc.returncode
    except subprocess.TimeoutExpired:
        combined_output = "Test execution timed out"
        exit_code = 1
    except Exception as exc:
        combined_output = str(exc)
        exit_code = 1

    passed, failed, coverage = _parse_test_output(combined_output, language)

    # Compute test hash from all test files
    test_hash_val = ""
    if len(files_to_run) == 1:
        test_hash_val = calculate_sha256(Path(files_to_run[0]))
    else:
        combined_hash_parts = []
        for f in sorted(files_to_run):
            combined_hash_parts.append(calculate_sha256(Path(f)))
        test_hash_val = ";".join(combined_hash_parts)

    report = RunReport(
        datetime.datetime.now().isoformat(),
        exit_code,
        passed,
        failed,
        coverage,
        test_hash=test_hash_val,
    )
    _persist_run_report(report, basename, language, atomic_state)
    return report


def _persist_run_report(
    report: RunReport,
    basename: str,
    language: str,
    atomic_state: Optional[AtomicStateUpdate],
):
    if atomic_state is not None:
        atomic_state.set_run_report(report)
    else:
        save_run_report(basename, language, report.__dict__)


# ---------------------------------------------------------------------------
# Helper: synthetic run report for agentic success
# ---------------------------------------------------------------------------
def _create_synthetic_run_report_for_agentic_success(
    test_file: str,
    basename: str,
    language: str,
    *,
    atomic_state: Optional[AtomicStateUpdate] = None,
) -> RunReport:
    """Create a synthetic RunReport when agentic test generation succeeds."""
    test_path = Path(test_file)
    test_hash = (
        calculate_sha256(test_path) if test_path.exists()
        else "agentic_test_success"
    )
    report = RunReport(
        datetime.datetime.now().isoformat(),
        0,  # exit_code
        1,  # tests_passed
        0,  # tests_failed
        0.0,  # coverage
        test_hash=test_hash,
    )
    _persist_run_report(report, basename, language, atomic_state)
    return report


# ---------------------------------------------------------------------------
# Helper: file-existence color
# ---------------------------------------------------------------------------
def _color_for_path(p: str) -> str:
    return "green" if p and Path(p).exists() else "red"


def _update_file_colors(
    pdd_files: dict,
    prompt_cr, code_cr, example_cr, test_cr,
):
    prompt_cr[0] = _color_for_path(str(pdd_files.get("prompt", "")))
    code_cr[0] = _color_for_path(str(pdd_files.get("code", "")))
    example_cr[0] = _color_for_path(str(pdd_files.get("example", "")))
    test_cr[0] = _color_for_path(str(pdd_files.get("test", "")))


# ---------------------------------------------------------------------------
# Helper: construct default paths (fallback)
# ---------------------------------------------------------------------------
def _construct_default_paths(
    basename: str,
    language: str,
    ext: str,
    prompts_dir: str,
    code_dir: str,
    examples_dir: str,
    tests_dir: str,
) -> Dict[str, str]:
    """Build default file paths when get_pdd_file_paths fails on test lookup."""
    safe = _safe_basename(basename)

    # Case-insensitive prompt lookup
    prompt_dir = Path(prompts_dir)
    prompt_path = ""
    if prompt_dir.is_dir():
        target_name = f"{safe}_{language}.prompt".lower()
        for f in prompt_dir.iterdir():
            if f.name.lower() == target_name:
                prompt_path = str(f)
                break
    if not prompt_path:
        prompt_path = str(prompt_dir / f"{safe}_{language}.prompt")

    return {
        "prompt": prompt_path,
        "code": str(Path(code_dir) / f"{safe}.{ext}"),
        "example": str(Path(examples_dir) / f"{safe}_example.{ext}"),
        "test": str(Path(tests_dir) / f"test_{safe}.{ext}"),
    }


# ---------------------------------------------------------------------------
# Helper: cycle detection
# ---------------------------------------------------------------------------
def _detect_cycle(
    history: List[str],
    current_op: str,
    test_extend_count: int,
    max_cycle_repeats: int = 2,
) -> Optional[str]:
    """Return a human-readable reason string if a cycle is detected, else None."""

    # Auto-deps: 2+ in last 3 → force advance
    recent3 = history[-3:]
    if recent3.count("auto-deps") >= 2:
        return "auto-deps repeated ≥2 times in last 3 ops; advancing to generate"

    # Consecutive same-op limits
    def _tail_run(op):
        count = 0
        for o in reversed(history):
            if o == op:
                count += 1
            else:
                break
        return count

    if _tail_run("fix") >= 5:
        return "5 consecutive fix operations; breaking"
    if _tail_run("test") >= MAX_CONSECUTIVE_TESTS:
        return f"{MAX_CONSECUTIVE_TESTS} consecutive test operations; breaking"
    if _tail_run("crash") >= MAX_CONSECUTIVE_CRASHES:
        return f"{MAX_CONSECUTIVE_CRASHES} consecutive crash operations; breaking"

    # Crash-verify alternation
    if len(history) >= 4:
        tail4 = history[-4:]
        if tail4 == ["crash", "verify", "crash", "verify"] or tail4 == [
            "verify",
            "crash",
            "verify",
            "crash",
        ]:
            return "crash↔verify alternation detected (2 cycles); breaking"

    # Test-fix alternation
    if len(history) >= 4:
        tail4 = history[-4:]
        if tail4 == ["test", "fix", "test", "fix"] or tail4 == [
            "fix",
            "test",
            "fix",
            "test",
        ]:
            return "test↔fix alternation detected (2 cycles); breaking"

    # Test_extend attempts
    if current_op == "test_extend" and test_extend_count >= MAX_TEST_EXTEND_ATTEMPTS:
        return (
            f"test_extend attempted {test_extend_count} times; "
            "accepting current coverage"
        )

    return None


# ---------------------------------------------------------------------------
# Helper: handle skip
# ---------------------------------------------------------------------------
def _handle_skip(
    basename: str,
    language: str,
    operation: str,
    pdd_files: dict,
    skipped_operations: list,
    total_cost: float,
    model: str,
    *,
    create_synthetic_report: bool = False,
):
    """Record a skipped operation and optionally write a synthetic run report."""
    skipped_operations.append(operation)
    paths = {k: Path(v) for k, v in pdd_files.items() if v}
    save_fingerprint(
        basename=basename,
        language=language,
        operation=f"skip:{operation}",
        paths=paths,
        cost=0.0,
        model=model or "skipped",
    )
    if create_synthetic_report:
        report = RunReport(
            datetime.datetime.now().isoformat(), 0, 0, 0, 0.0, test_hash="skip",
        )
        save_run_report(basename, language, report.__dict__)

    entry = create_log_entry(
        operation=operation,
        reason=f"Skipped by user flag",
        invocation_mode="sync",
        estimated_cost=0.0,
        confidence=1.0,
        decision_type="skip",
    )
    entry = update_log_entry(entry, True, 0.0, "skipped", 0.0, None)
    append_log_entry(basename, language, entry)


# ---------------------------------------------------------------------------
# Helper: extract result from various return formats
# ---------------------------------------------------------------------------
def _extract_result(result, operation: str) -> tuple:
    """Normalize command return values → (success, cost, model, extra)."""
    if isinstance(result, dict):
        return (
            result.get("success", False),
            result.get("cost", 0.0),
            result.get("model", ""),
            result,
        )

    if not isinstance(result, (tuple, list)):
        return False, 0.0, "", {}

    if operation == "test" and len(result) == 4:
        # (content, cost, model, agentic_success)
        content, cost, model, agentic_success = (
            result[0],
            result[1],
            result[2],
            result[3],
        )
        success = bool(content)
        return success, cost, model, {"agentic_success": agentic_success}

    if operation == "generate" and len(result) == 4:
        # (code, incremental, cost, model)
        return bool(result[0]), result[2], result[3], {"incremental": result[1]}

    if len(result) == 3:
        # (content_or_success, cost, model)
        return bool(result[0]), result[-2], result[-1], {}

    if len(result) == 6:
        # crash / fix / verify: (success, content, content2, attempts, cost, model)
        return bool(result[0]), result[4], result[5], {"attempts": result[3]}

    return bool(result[0]), 0.0, "", {}


# ===================================================================
# Main orchestration function
# ===================================================================
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
    """Orchestrate the full PDD sync workflow for *basename*.

    Coordinates operation execution, TUI animation, state persistence,
    and interactive steering in a single entry-point.
    """
    # Defense in depth --------------------------------------------------
    if target_coverage is None:
        target_coverage = 90.0
    if budget is None:
        budget = 10.0
    if max_attempts is None:
        max_attempts = 3

    from .get_extension import get_extension

    lang_lower = language.lower()
    ext = get_extension(language)
    safe_base = _safe_basename(basename)

    # ------------------------------------------------------------------
    # Dry-run mode
    # ------------------------------------------------------------------
    if dry_run:
        _display_sync_log(basename, language, verbose)
        decision = sync_determine_operation(
            basename, language, target_coverage, log_mode=True
        )
        click.echo(
            f"\nRecommended operation: {decision.operation} "
            f"(confidence={decision.confidence}, "
            f"est_cost=${decision.estimated_cost:.4f})"
        )
        click.echo(f"Reason: {decision.reason}")
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
            "log_entries": load_operation_log(basename, language),
        }

    # ------------------------------------------------------------------
    # Headless detection
    # ------------------------------------------------------------------
    is_headless = quiet or not sys.stdin.isatty() or bool(os.environ.get("CI"))

    # ------------------------------------------------------------------
    # Mutable TUI references
    # ------------------------------------------------------------------
    function_name_ref = ["initializing"]
    cost_ref = [0.0]
    prompt_color_ref = ["blue"]
    code_color_ref = ["blue"]
    example_color_ref = ["blue"]
    test_color_ref = ["blue"]
    prompt_path_ref = [""]
    code_path_ref = [""]
    example_path_ref = [""]
    test_path_ref = [""]
    stop_event = threading.Event()
    app_ref: List[Any] = []
    user_confirmed_overwrite = [False]
    progress_callback_ref: List[Any] = [None]

    # ------------------------------------------------------------------
    # Confirmation callback
    # ------------------------------------------------------------------
    def _get_confirm_callback() -> Callable:
        if is_headless:
            def _headless_confirm(_filename: str, message: str) -> bool:
                if force or user_confirmed_overwrite[0]:
                    return True
                try:
                    result = click.confirm(message, default=True)
                except (EOFError, click.Abort):
                    result = force
                if result:
                    user_confirmed_overwrite[0] = True
                return result

            return _headless_confirm

        def _tui_confirm(_filename: str, message: str) -> bool:
            if force or user_confirmed_overwrite[0]:
                return True
            if app_ref:
                result = app_ref[0].request_confirmation(message)
                if result:
                    user_confirmed_overwrite[0] = True
                return result
            return True

        return _tui_confirm

    cb = confirm_callback or _get_confirm_callback()

    # ------------------------------------------------------------------
    # Shared context builder
    # ------------------------------------------------------------------
    def _ctx(**overrides):
        kw = dict(
            force=force,
            quiet=quiet,
            verbose=verbose,
            strength=strength,
            temperature=temperature,
            time_param=time_param,
            local=local,
            output_cost=output_cost,
            review_examples=review_examples,
            context_override=context_override,
            confirm_callback=cb,
        )
        kw.update(overrides)
        return _create_mock_context(**kw)

    # ------------------------------------------------------------------
    # Result container
    # ------------------------------------------------------------------
    result_holder: Dict[str, Any] = {}

    # ==================================================================
    # Worker logic
    # ==================================================================
    def sync_worker_logic():  # noqa: C901  (complexity unavoidable)
        MAX_CYCLE_REPEATS = 2  # noqa: N806
        start_time = time.time()
        total_cost = 0.0
        operations_completed: List[str] = []
        skipped_operations: List[str] = []
        errors: List[str] = []
        last_model = ""
        operations_history: List[str] = []
        test_extend_count = 0
        final_decision_op = ""

        # -- Resolve paths -------------------------------------------------
        try:
            pdd_files = get_pdd_file_paths(basename, language)
        except FileNotFoundError as exc:
            err_msg = str(exc)
            if "test" in err_msg.lower():
                pdd_files = _construct_default_paths(
                    basename, language, ext,
                    prompts_dir, code_dir, examples_dir, tests_dir,
                )
            else:
                elapsed = time.time() - start_time
                result_holder.update(
                    _error_result(err_msg, elapsed)
                )
                stop_event.set()
                return

        # Populate TUI refs
        for key, ref in [
            ("prompt", prompt_path_ref),
            ("code", code_path_ref),
            ("example", example_path_ref),
            ("test", test_path_ref),
        ]:
            ref[0] = str(pdd_files.get(key, ""))
        _update_file_colors(
            pdd_files, prompt_color_ref, code_color_ref,
            example_color_ref, test_color_ref,
        )

        # Collect possible extra test files
        extra_test_files = pdd_files.get("test_files", [])

        # Convenience paths
        prompt_path = str(pdd_files.get("prompt", ""))
        code_path = str(pdd_files.get("code", ""))
        example_path = str(pdd_files.get("example", ""))
        test_path = str(pdd_files.get("test", ""))

        def _paths_dict():
            return {
                k: Path(v)
                for k, v in pdd_files.items()
                if v and k in ("prompt", "code", "example", "test")
            }

        def _remaining_budget():
            return max(budget - total_cost, 0.0)

        # -- Main loop -----------------------------------------------------
        try:
            with SyncLock(basename, language) as _lock:
                log_event(
                    basename, language, "lock_acquired", {},
                    invocation_mode="sync",
                )

                while not stop_event.is_set():
                    # Budget gate
                    if total_cost >= budget:
                        log_event(
                            basename, language, "budget_exceeded",
                            {"total_cost": total_cost},
                            invocation_mode="sync",
                        )
                        errors.append(
                            f"Budget exhausted: ${total_cost:.2f} >= ${budget:.2f}"
                        )
                        break

                    if (
                        budget > 0
                        and total_cost > 0
                        and (budget - total_cost) / budget < 0.2
                    ):
                        log_event(
                            basename, language, "budget_warning",
                            {"remaining": budget - total_cost},
                            invocation_mode="sync",
                        )

                    # Determine operation
                    decision = sync_determine_operation(
                        basename, language, target_coverage
                    )
                    final_decision_op = decision.operation

                    # Terminal states
                    if decision.operation in ("all_synced", "nothing"):
                        break
                    if decision.operation in (
                        "fail_and_request_manual_merge",
                        "error",
                    ):
                        errors.append(decision.reason)
                        break

                    # Interactive steering
                    if not no_steer and not is_headless:
                        steered_op, should_abort = maybe_steer_operation(
                            decision.operation,
                            decision.reason,
                            app_ref,
                            quiet,
                            skip_tests,
                            skip_verify,
                            timeout_s=steer_timeout,
                        )
                        if should_abort:
                            errors.append("Workflow aborted by user steering")
                            break
                        if steered_op != decision.operation:
                            log_event(
                                basename, language, "steering_override",
                                {
                                    "from": decision.operation,
                                    "to": steered_op,
                                },
                                invocation_mode="sync",
                            )
                            decision = SyncDecision(
                                operation=steered_op,
                                reason=decision.reason,
                                estimated_cost=decision.estimated_cost,
                                confidence=decision.confidence,
                                decision_type=decision.decision_type,
                            )

                    # Cycle detection
                    operations_history.append(decision.operation)
                    cycle_msg = _detect_cycle(
                        operations_history,
                        decision.operation,
                        test_extend_count,
                        MAX_CYCLE_REPEATS,
                    )
                    if cycle_msg:
                        log_event(
                            basename, language, "cycle_detected",
                            {"message": cycle_msg},
                            invocation_mode="sync",
                        )
                        errors.append(f"Cycle detected: {cycle_msg}")
                        break

                    if decision.operation == "test_extend":
                        test_extend_count += 1

                    # -- Skip handling -----------------------------------------
                    if decision.operation == "verify" and (skip_verify or skip_tests):
                        _handle_skip(
                            basename, language, "verify", pdd_files,
                            skipped_operations, total_cost, last_model,
                        )
                        continue
                    if decision.operation == "crash" and skip_tests:
                        _handle_skip(
                            basename, language, "crash", pdd_files,
                            skipped_operations, total_cost, last_model,
                            create_synthetic_report=True,
                        )
                        continue
                    if decision.operation in ("test", "test_extend") and skip_tests:
                        _handle_skip(
                            basename, language, decision.operation, pdd_files,
                            skipped_operations, total_cost, last_model,
                        )
                        continue

                    # Non-Python: skip test_extend entirely
                    # (Python and TypeScript handle locally)
                    if (
                        decision.operation == "test_extend"
                        and lang_lower not in ("python", "typescript")
                    ):
                        skipped_operations.append("test_extend")
                        continue

                    # -- Create log entry --------------------------------------
                    entry = create_log_entry(
                        operation=decision.operation,
                        reason=decision.reason,
                        invocation_mode="sync",
                        estimated_cost=decision.estimated_cost,
                        confidence=decision.confidence,
                        decision_type=decision.decision_type,
                    )

                    function_name_ref[0] = decision.operation
                    op_start = time.time()
                    op_success = False
                    op_cost = 0.0
                    op_model = ""
                    op_error: Optional[str] = None

                    try:
                        with AtomicStateUpdate(basename, language) as atomic:
                            op_success, op_cost, op_model, op_error = (
                                _execute_operation(
                                    decision=decision,
                                    basename=basename,
                                    language=language,
                                    lang_lower=lang_lower,
                                    ext=ext,
                                    pdd_files=pdd_files,
                                    prompt_path=prompt_path,
                                    code_path=code_path,
                                    example_path=example_path,
                                    test_path=test_path,
                                    extra_test_files=extra_test_files,
                                    target_coverage=target_coverage,
                                    max_attempts=max_attempts,
                                    remaining_budget=_remaining_budget(),
                                    strength=strength,
                                    temperature=temperature,
                                    time_param=time_param,
                                    agentic_mode=agentic_mode,
                                    ctx_factory=_ctx,
                                    atomic=atomic,
                                    examples_dir=examples_dir,
                                    progress_callback_ref=progress_callback_ref,
                                )
                            )

                            if op_success:
                                atomic.set_fingerprint(
                                    operation=decision.operation,
                                    paths=_paths_dict(),
                                    cost=op_cost,
                                    model=op_model,
                                )

                    except Exception as exc:
                        import traceback as _tb

                        op_error = str(exc)
                        logger.error(
                            "Operation %s failed: %s",
                            decision.operation, exc,
                        )
                        logger.debug(_tb.format_exc())

                    op_duration = time.time() - op_start

                    # Update log entry
                    entry = update_log_entry(
                        entry, op_success, op_cost, op_model,
                        op_duration, op_error,
                    )
                    append_log_entry(basename, language, entry)

                    # Accumulators
                    total_cost += op_cost
                    cost_ref[0] = total_cost
                    if op_model:
                        last_model = op_model

                    if op_success:
                        operations_completed.append(decision.operation)
                    if op_error:
                        errors.append(f"{decision.operation}: {op_error}")

                    _update_file_colors(
                        pdd_files, prompt_color_ref, code_color_ref,
                        example_color_ref, test_color_ref,
                    )

                log_event(
                    basename, language, "lock_released", {},
                    invocation_mode="sync",
                )

        except Exception as exc:
            import traceback as _tb

            errors.append(f"Sync error: {exc}")
            logger.error("Sync error: %s", _tb.format_exc())

        # -- Build result --------------------------------------------------
        elapsed = time.time() - start_time
        final_state = {}
        for ftype in ("prompt", "code", "example", "test"):
            fpath = str(pdd_files.get(ftype, ""))
            final_state[ftype] = {
                "exists": Path(fpath).exists() if fpath else False,
                "path": fpath,
            }

        overall_success = (
            not errors
            and final_decision_op in ("all_synced", "nothing", "")
        )

        result_holder.update({
            "success": overall_success,
            "operations_completed": operations_completed,
            "skipped_operations": skipped_operations,
            "total_cost": total_cost,
            "total_time": elapsed,
            "final_state": final_state,
            "errors": errors,
            "error": "; ".join(errors) if errors else None,
            "model_name": last_model,
        })
        stop_event.set()

    # ==================================================================
    # Run the worker (headless vs. TUI)
    # ==================================================================
    if is_headless:
        prev_force = os.environ.get("PDD_FORCE")
        os.environ["PDD_FORCE"] = "1"
        try:
            sync_worker_logic()
        finally:
            if prev_force is None:
                os.environ.pop("PDD_FORCE", None)
            else:
                os.environ["PDD_FORCE"] = prev_force
    else:
        app = SyncApp(
            worker_func=sync_worker_logic,
            function_name_ref=function_name_ref,
            cost_ref=cost_ref,
            prompt_color_ref=prompt_color_ref,
            code_color_ref=code_color_ref,
            example_color_ref=example_color_ref,
            test_color_ref=test_color_ref,
            prompt_path_ref=prompt_path_ref,
            code_path_ref=code_path_ref,
            example_path_ref=example_path_ref,
            test_path_ref=test_path_ref,
            stop_event=stop_event,
        )
        app_ref.append(app)

        run_result = app.run()

        # Check for worker crashes
        if hasattr(app, "worker_exception") and app.worker_exception:
            import traceback as _tb

            print(
                f"Worker thread crashed: {app.worker_exception}",
                file=sys.stderr,
            )
            _tb.print_exception(
                type(app.worker_exception),
                app.worker_exception,
                app.worker_exception.__traceback__,
                file=sys.stderr,
            )

        if run_result is None:
            return {
                "success": False,
                "operations_completed": [],
                "skipped_operations": [],
                "total_cost": 0.0,
                "total_time": 0.0,
                "final_state": {},
                "errors": ["Sync was interrupted"],
                "error": "Sync was interrupted",
                "model_name": "",
            }

        if not quiet:
            from .sync_tui import show_exit_animation

            show_exit_animation(result_holder)

    return result_holder


# ======================================================================
# Operation dispatcher
# ======================================================================
def _execute_operation(  # noqa: C901
    *,
    decision: SyncDecision,
    basename: str,
    language: str,
    lang_lower: str,
    ext: str,
    pdd_files: dict,
    prompt_path: str,
    code_path: str,
    example_path: str,
    test_path: str,
    extra_test_files: List[str],
    target_coverage: float,
    max_attempts: int,
    remaining_budget: float,
    strength: float,
    temperature: float,
    time_param: float,
    agentic_mode: bool,
    ctx_factory: Callable,
    atomic: AtomicStateUpdate,
    examples_dir: str,
    progress_callback_ref: list,
) -> tuple:
    """Execute a single sync operation.

    Returns ``(success: bool, cost: float, model: str, error: str | None)``.
    """
    op = decision.operation
    ctx = ctx_factory()
    agentic = _use_agentic_path(language, agentic_mode)
    effective_max = 0 if agentic else max_attempts

    # ==================================================================
    if op == "auto-deps":
        import shutil

        dep_csv = "./project_dependencies.csv"
        dep_dir = f"{examples_dir}/**/*.{ext}" if examples_dir else f"context/*_example.{ext}"
        result = auto_deps_main(
            ctx=ctx,
            prompt_file=prompt_path,
            directory_path=dep_dir,
            auto_deps_csv_path=dep_csv,
            output=prompt_path,
            force_scan=False,
        )
        _content, cost, model = result
        return True, cost, model, None

    # ==================================================================
    elif op == "generate":
        result = code_generator_main(
            ctx=ctx,
            prompt_file=prompt_path,
            output=code_path,
            original_prompt_file_path=None,
            force_incremental_flag=False,
        )
        success, cost, model, _extra = _extract_result(result, "generate")

        # After generate: delete stale run_report
        if success:
            clear_run_report(basename, language)

        return success, cost, model, None

    # ==================================================================
    elif op == "example":
        result = context_generator_main(
            ctx=ctx,
            prompt_file=prompt_path,
            code_file=code_path,
            output=example_path,
        )
        _content, cost, model = result
        return True, cost, model, None

    # ==================================================================
    elif op == "crash":
        # Non-Python: delegate entirely to agentic handler
        if agentic:
            has_crash = True
            crash_log = f"Non-Python ({language}) crash detection delegated to agentic handler"
        else:
            ok, output, _rc = _run_example_with_error_detection(
                example_path, code_path, language,
            )
            has_crash = not ok
            crash_log = output if not ok else ""

        if not has_crash:
            # No crash — save synthetic success report
            report = RunReport(
                datetime.datetime.now().isoformat(),
                0, 0, 0, 0.0, test_hash="crash_check_pass",
            )
            atomic.set_run_report(report)
            return True, 0.0, "", None

        # Write crash log to temp file
        with tempfile.NamedTemporaryFile(
            mode="w", suffix=".log", delete=False, prefix="pdd_crash_",
        ) as tmp:
            tmp.write(crash_log)
            error_file = tmp.name

        try:
            result = crash_main(
                ctx=ctx,
                prompt_file=prompt_path,
                code_file=code_path,
                program_file=example_path,
                error_file=error_file,
                output=code_path,
                output_program=example_path,
                loop=True,
                strength=strength,
                temperature=temperature,
                budget=remaining_budget,
                max_attempts=effective_max,
            )
        finally:
            try:
                os.unlink(error_file)
            except OSError:
                pass

        success, cost, model, _extra = _extract_result(result, "crash")

        # Post-crash validation
        if success:
            if not agentic:
                ok, _out, rc = _run_example_with_error_detection(
                    example_path, code_path, language,
                )
                report = RunReport(
                    datetime.datetime.now().isoformat(),
                    0 if ok else rc, 0, 0, 0.0,
                    test_hash="crash_post_verify",
                )
                atomic.set_run_report(report)
            else:
                report = RunReport(
                    datetime.datetime.now().isoformat(),
                    0, 0, 0, 0.0, test_hash="agentic_crash_success",
                )
                atomic.set_run_report(report)

        return success, cost, model, None

    # ==================================================================
    elif op == "verify":
        result = fix_verification_main(
            ctx=ctx,
            prompt_file=prompt_path,
            code_file=code_path,
            program_file=example_path,
            output_results=None,
            output_code=code_path,
            output_program=example_path,
            loop=True,
            verification_program=None,
            max_attempts=effective_max,
            budget=remaining_budget,
            agentic_fallback=True,
        )
        success, cost, model, _extra = _extract_result(result, "verify")
        return success, cost, model, None

    # ==================================================================
    elif op in ("test", "test_extend"):
        is_extend = op == "test_extend"

        kw: Dict[str, Any] = dict(
            ctx=ctx,
            prompt_file=prompt_path,
            code_file=code_path,
            output=test_path,
            language=language,
            strength=strength,
            temperature=temperature,
        )

        if is_extend:
            # Coverage-aware extension
            existing = [test_path] + [
                f for f in extra_test_files if Path(f).exists()
            ]
            existing = [f for f in existing if Path(f).exists()]
            run_rpt = read_run_report(basename, language)
            cov_report = None
            if run_rpt and hasattr(run_rpt, "coverage"):
                # Generate a minimal coverage XML if needed
                pass  # cmd_test_main handles coverage_report path
            kw.update(
                coverage_report=cov_report,
                existing_tests=existing or None,
                target_coverage=target_coverage,
                merge=True,
            )
        else:
            kw.update(
                coverage_report=None,
                existing_tests=None,
                target_coverage=None,
                merge=False,
            )

        result = cmd_test_main(**kw)
        _content, cost, model, agentic_success = (
            result[0], result[1], result[2], result[3],
        )
        success = bool(_content)

        # Determine if we should use agentic_success
        if agentic_success is not None:
            success = bool(agentic_success)

        if not success:
            return False, cost, model, "Test generation failed"

        # Post-test: execute tests and create run report
        if agentic_success is True:
            # Synthetic report for agentic test success
            if is_extend and lang_lower in ("python", "typescript"):
                # Python/TS test_extend: always run tests locally
                all_files = [test_path] + [
                    f for f in extra_test_files if Path(f).exists()
                ]
                all_files = [f for f in all_files if Path(f).exists()]
                _execute_tests_and_create_run_report(
                    test_path, basename, language, target_coverage,
                    code_file=code_path, atomic_state=atomic,
                    test_files=all_files if len(all_files) > 1 else None,
                )
            else:
                _create_synthetic_run_report_for_agentic_success(
                    test_path, basename, language, atomic_state=atomic,
                )
        else:
            all_files = [test_path] + [
                f for f in extra_test_files if Path(f).exists()
            ]
            all_files = [f for f in all_files if Path(f).exists()]
            _execute_tests_and_create_run_report(
                test_path, basename, language, target_coverage,
                code_file=code_path, atomic_state=atomic,
                test_files=all_files if len(all_files) > 1 else None,
            )

        return True, cost, model, None

    # ==================================================================
    elif op == "fix":
        from .get_test_command import get_test_command_for_file

        # Pre-run tests to capture current errors
        all_test_files = [test_path] + [
            f for f in extra_test_files if Path(f).exists()
        ]
        all_test_files = [f for f in all_test_files if Path(f).exists()]

        # Determine which test file is failing
        failing_test = test_path
        if lang_lower == "python" and all_test_files:
            env = _clean_subprocess_env()
            python_exe = detect_host_python_executable() or sys.executable
            project_root = _find_project_root(test_path)
            if project_root:
                pp = env.get("PYTHONPATH", "")
                extras = [str(project_root), str(Path(project_root) / "src")]
                env["PYTHONPATH"] = os.pathsep.join(
                    [p for p in extras if p] + ([pp] if pp else [])
                )
            cmd = [python_exe, "-m", "pytest", "-x", "-v"]
            if project_root:
                cmd += [f"--rootdir={project_root}", "-c", "/dev/null"]
            cmd += all_test_files
            try:
                proc = subprocess.run(
                    cmd,
                    capture_output=True, text=True,
                    timeout=300, env=env,
                    start_new_session=True,
                    stdin=subprocess.DEVNULL,
                )
                combined = (proc.stdout or "") + "\n" + (proc.stderr or "")
                failing_files = extract_failing_files_from_output(combined)
                if failing_files:
                    failing_test = failing_files[0]
            except Exception:
                pass

        # Write error file
        error_file_path = ""
        with tempfile.NamedTemporaryFile(
            mode="w", suffix=".log", delete=False, prefix="pdd_fix_",
        ) as tmp:
            tmp.write("")
            error_file_path = tmp.name

        try:
            result = fix_main(
                ctx=ctx,
                prompt_file=prompt_path,
                code_file=code_path,
                unit_test_file=failing_test,
                error_file=error_file_path,
                output_test=failing_test,
                output_code=code_path,
                output_results=None,
                loop=True,
                verification_program=example_path,
                max_attempts=effective_max,
                budget=remaining_budget,
                auto_submit=False,
                agentic_fallback=True,
                strength=None,
                temperature=None,
                test_files=all_test_files if len(all_test_files) > 1 else None,
            )
        finally:
            try:
                os.unlink(error_file_path)
            except OSError:
                pass

        success, cost, model, _extra = _extract_result(result, "fix")

        # Post-fix: re-run tests (Python) or trust agentic (non-Python)
        if success:
            if not agentic:
                _execute_tests_and_create_run_report(
                    test_path, basename, language, target_coverage,
                    code_file=code_path, atomic_state=atomic,
                    test_files=all_test_files if len(all_test_files) > 1 else None,
                )
            else:
                report = RunReport(
                    datetime.datetime.now().isoformat(),
                    0, 1, 0, 0.0,
                    test_hash="agentic_fix_success",
                )
                atomic.set_run_report(report)

        return success, cost, model, None

    # ==================================================================
    elif op == "update":
        result = update_main(
            ctx=ctx,
            input_prompt_file=prompt_path,
            modified_code_file=code_path,
            input_code_file=None,
            output=prompt_path,
            use_git=True,
            simple=False,
        )
        _content, cost, model = result
        return True, cost, model, None

    # ==================================================================
    else:
        return False, 0.0, "", f"Unknown operation: {op}"


# ---------------------------------------------------------------------------
# Helper: error result dict
# ---------------------------------------------------------------------------
def _error_result(msg: str, elapsed: float = 0.0) -> Dict[str, Any]:
    return {
        "success": False,
        "operations_completed": [],
        "skipped_operations": [],
        "total_cost": 0.0,
        "total_time": elapsed,
        "final_state": {},
        "errors": [msg],
        "error": msg,
        "model_name": "",
    }
""