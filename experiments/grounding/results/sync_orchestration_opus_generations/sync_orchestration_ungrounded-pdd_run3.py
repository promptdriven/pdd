"""
PDD Sync Orchestration Module.

Coordinates the complete PDD sync workflow by executing operations
(auto-deps, generate, example, crash, verify, test, fix, update)
determined by sync_determine_operation, while providing real-time
visual feedback via the Textual-based TUI.
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

TERMINAL_STATES = frozenset(
    {"all_synced", "nothing", "fail_and_request_manual_merge", "error"}
)

COLOR_GREEN = "green"
COLOR_YELLOW = "yellow"
COLOR_RED = "red"
COLOR_BLUE = "blue"


# ---------------------------------------------------------------------------
# AtomicStateUpdate
# ---------------------------------------------------------------------------


class AtomicStateUpdate:
    """Context manager ensuring run_report and fingerprint are both written
    or neither is written.  Uses temp-file + atomic rename for crash safety."""

    def __init__(self, basename: str, language: str):
        self.basename = basename
        self.language = language
        self._pending_run_report: Optional[dict] = None
        self._pending_fingerprint: Optional[dict] = None

    # -- public API used by callers -------------------------------------------

    def set_run_report(self, report_data: dict) -> None:
        self._pending_run_report = report_data

    def set_fingerprint(self, **kwargs: Any) -> None:
        self._pending_fingerprint = kwargs

    # -- context manager ------------------------------------------------------

    def __enter__(self) -> "AtomicStateUpdate":
        return self

    def __exit__(self, exc_type, exc_val, exc_tb) -> bool:
        if exc_type is not None:
            return False
        self.commit()
        return False

    def commit(self) -> None:
        meta = Path.cwd() / PDD_DIR / META_DIR
        meta.mkdir(parents=True, exist_ok=True)
        safe_bn = _safe_basename(self.basename)
        lang = self.language.lower()

        tmp_paths: List[tuple] = []
        try:
            if self._pending_run_report is not None:
                target = meta / f"{safe_bn}_{lang}_run.json"
                fd, tmp_name = tempfile.mkstemp(dir=str(meta), suffix=".tmp")
                try:
                    with os.fdopen(fd, "w", encoding="utf-8") as fh:
                        json.dump(self._pending_run_report, fh)
                except Exception:
                    os.close(fd)
                    raise
                tmp_paths.append((Path(tmp_name), target))

            if self._pending_fingerprint is not None:
                save_fingerprint(
                    basename=self.basename,
                    language=self.language,
                    **self._pending_fingerprint,
                )

            for tmp, target in tmp_paths:
                tmp.replace(target)

        except Exception:
            for tmp, _ in tmp_paths:
                try:
                    tmp.unlink(missing_ok=True)
                except Exception:
                    pass
            raise


# ---------------------------------------------------------------------------
# Helpers – TUI colour/path updates
# ---------------------------------------------------------------------------


def _update_file_colors(
    pdd_files: Dict[str, Any],
    prompt_color_ref: list,
    code_color_ref: list,
    example_color_ref: list,
    test_color_ref: list,
    prompt_path_ref: list,
    code_path_ref: list,
    example_path_ref: list,
    test_path_ref: list,
) -> None:
    """Refresh TUI colour/path refs from current file state."""
    mapping = {
        "prompt": (prompt_color_ref, prompt_path_ref),
        "code": (code_color_ref, code_path_ref),
        "example": (example_color_ref, example_path_ref),
        "test": (test_color_ref, test_path_ref),
    }
    for key, (color_ref, path_ref) in mapping.items():
        p = pdd_files.get(key)
        if p:
            path_ref[0] = str(p)
            color_ref[0] = COLOR_GREEN if Path(p).exists() else COLOR_RED
        else:
            path_ref[0] = ""
            color_ref[0] = COLOR_RED


def _set_active_color(
    operation: str,
    prompt_color_ref: list,
    code_color_ref: list,
    example_color_ref: list,
    test_color_ref: list,
) -> None:
    """Set the file being worked on to yellow (processing)."""
    op_to_ref = {
        "auto-deps": prompt_color_ref,
        "generate": code_color_ref,
        "example": example_color_ref,
        "crash": code_color_ref,
        "verify": code_color_ref,
        "test": test_color_ref,
        "test_extend": test_color_ref,
        "fix": test_color_ref,
        "update": prompt_color_ref,
    }
    ref = op_to_ref.get(operation)
    if ref is not None:
        ref[0] = COLOR_YELLOW


# ---------------------------------------------------------------------------
# Helpers – Mock click context
# ---------------------------------------------------------------------------


def _create_mock_context(
    strength: float = DEFAULT_STRENGTH,
    temperature: float = 0.0,
    time_param: float = 0.25,
    verbose: bool = False,
    quiet: bool = False,
    force: bool = False,
    local: bool = False,
    review_examples: bool = False,
    output_cost: Optional[str] = None,
    context_override: Optional[str] = None,
    confirm_callback: Optional[Callable] = None,
) -> click.Context:
    ctx = click.Context(click.Command("sync"))
    ctx.obj = {
        "strength": strength,
        "temperature": temperature,
        "time": time_param,
        "verbose": verbose,
        "quiet": quiet,
        "force": force,
        "local": local,
        "review_examples": review_examples,
        "output_cost": output_cost,
        "context": context_override,
        "confirm_callback": confirm_callback,
    }
    ctx.params = {
        "local": local,
        "force": force,
        "quiet": quiet,
    }
    return ctx


# ---------------------------------------------------------------------------
# Helpers – test output parsing
# ---------------------------------------------------------------------------


def _parse_test_output(
    output: str, language: str
) -> tuple:
    """Parse test runner output.

    Returns ``(tests_passed, tests_failed, coverage)``.
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
        # pytest-cov TOTAL line
        m = re.search(r"TOTAL\s+\d+\s+\d+\s+(\d+)%", output)
        if m:
            coverage = float(m.group(1))
    elif lang in ("javascript", "typescript"):
        # Jest / Vitest / Mocha
        m = re.search(r"Tests:\s+(?:.*?(\d+)\s+failed,?\s*)?(\d+)\s+passed", output)
        if m:
            tests_failed = int(m.group(1)) if m.group(1) else 0
            tests_passed = int(m.group(2))
        if tests_passed == 0 and tests_failed == 0:
            tests_passed = len(re.findall(r"[✓✅]|PASS|passing", output))
            tests_failed = len(re.findall(r"[✗✖❌]|FAIL|failing", output))
        m = re.search(r"(?:Stmts|Lines)\s*:\s*([\d.]+)%", output)
        if m:
            coverage = float(m.group(1))
    elif lang == "go":
        tests_passed = len(re.findall(r"--- PASS:", output))
        tests_failed = len(re.findall(r"--- FAIL:", output))
        m = re.search(r"coverage:\s+([\d.]+)%", output)
        if m:
            coverage = float(m.group(1))
    elif lang in ("rust", "cpp"):
        m = re.search(
            r"test result:.*?(\d+)\s+passed.*?(\d+)\s+failed", output
        )
        if m:
            tests_passed = int(m.group(1))
            tests_failed = int(m.group(2))
    else:
        tests_passed = len(re.findall(r"(?i)\bpass(?:ed)?\b", output))
        tests_failed = len(re.findall(r"(?i)\bfail(?:ed|ure)?\b", output))

    return tests_passed, tests_failed, coverage


# ---------------------------------------------------------------------------
# Helpers – Python coverage targets
# ---------------------------------------------------------------------------


def _python_cov_target_for_code_file(code_file: str) -> str:
    """Determine dotted module path for pytest ``--cov`` target."""
    p = Path(code_file)
    parts = list(p.with_suffix("").parts)
    if parts and parts[0] == "src":
        parts = parts[1:]
    return ".".join(parts) if parts else p.stem


def _python_cov_target_for_test_and_code(
    test_file: str, code_file: str, fallback: str
) -> str:
    """Analyse test imports to pick the best ``--cov`` target."""
    try:
        content = Path(test_file).read_text(encoding="utf-8")
        code_stem = Path(code_file).stem
        imports = re.findall(r"(?:from|import)\s+([\w.]+)", content)
        for imp in imports:
            parts = imp.split(".")
            if code_stem in parts:
                return parts[0]
    except Exception:
        pass
    return fallback


# ---------------------------------------------------------------------------
# Helpers – example error detection
# ---------------------------------------------------------------------------


def _detect_example_errors(output: str) -> List[str]:
    """Detect Python tracebacks and ERROR log messages in *output*."""
    errors: List[str] = []
    lines = output.split("\n")
    tb_start: Optional[int] = None
    for i, line in enumerate(lines):
        if "Traceback (most recent call last)" in line:
            tb_start = i
        elif tb_start is not None and line and not line.startswith(" "):
            errors.append("\n".join(lines[tb_start : i + 1]))
            tb_start = None
    if tb_start is not None:
        errors.append("\n".join(lines[tb_start:]))

    for line in lines:
        if re.search(r"\bERROR\b", line):
            stripped = line.strip()
            if stripped and stripped not in errors:
                errors.append(stripped)
    return errors


def _run_example_with_error_detection(
    example_path: str,
    code_path: str,
    language: str,
) -> tuple:
    """Run example with timeout; handle server-style examples that block.

    Returns ``(success, stdout, stderr)``.
    """
    run_cmd = get_run_command_for_file(example_path, language=language)
    if not run_cmd:
        if language.lower() == "python":
            python_exec = detect_host_python_executable()
            run_cmd = f"{python_exec} {example_path}"
        else:
            return False, "", "No run command found for example"

    env = os.environ.copy()
    for var in ("FORCE_COLOR", "COLUMNS"):
        env.pop(var, None)

    project_root = _find_project_root(example_path) or Path.cwd()
    pp = [str(project_root)]
    src = project_root / "src"
    if src.is_dir():
        pp.insert(0, str(src))
    env["PYTHONPATH"] = os.pathsep.join(pp)

    try:
        result = subprocess.run(
            run_cmd,
            shell=True,
            capture_output=True,
            text=True,
            timeout=30,
            env=env,
            start_new_session=True,
            stdin=subprocess.DEVNULL,
        )
        combined = result.stdout + "\n" + result.stderr
        errs = _detect_example_errors(combined)
        return result.returncode == 0 and not errs, result.stdout, result.stderr
    except subprocess.TimeoutExpired:
        return True, "", "Process timed out (may be a long-running server)"
    except Exception as exc:
        return False, "", str(exc)


def _try_auto_fix_import_error(
    error_output: str, code_path: str, example_path: str
) -> bool:
    """Attempt to auto-fix a common ``ImportError`` before expensive agentic
    calls.  Returns ``True`` if a fix was applied."""
    m = re.search(
        r"(?:ModuleNotFoundError|ImportError):\s+(?:No module named\s+)?['\"]?(\w+)['\"]?",
        error_output,
    )
    if not m:
        return False

    missing = m.group(1)
    code_stem = Path(code_path).stem

    if missing == code_stem:
        code_dir = str(Path(code_path).parent.resolve())
        try:
            content = Path(example_path).read_text(encoding="utf-8")
        except Exception:
            return False
        if "sys.path.insert" not in content:
            fix = f"import sys; sys.path.insert(0, {code_dir!r})\n"
            Path(example_path).write_text(fix + content, encoding="utf-8")
            return True
    return False


# ---------------------------------------------------------------------------
# Helpers – test execution & run-report creation
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
) -> tuple:
    """Run tests and create/save a ``RunReport``.

    Returns ``(RunReport | None, raw_output_str)``.
    """
    from .get_test_command import get_test_command_for_file

    lang = language.lower()
    output = ""
    exit_code = 1

    env = os.environ.copy()
    for var in ("FORCE_COLOR", "COLUMNS"):
        env.pop(var, None)

    if lang == "python":
        python_exec = detect_host_python_executable()
        project_root = _find_project_root(test_file)

        if project_root:
            pp = str(project_root)
            src_dir = project_root / "src"
            if src_dir.is_dir():
                pp = f"{src_dir}{os.pathsep}{pp}"
            env["PYTHONPATH"] = pp

        files_to_test = (
            [str(f) for f in test_files] if test_files else [str(test_file)]
        )

        cmd: List[str] = [python_exec, "-m", "pytest"] + files_to_test + ["-v"]

        if code_file:
            fallback = _python_cov_target_for_code_file(code_file)
            cov_target = _python_cov_target_for_test_and_code(
                str(test_file), str(code_file), fallback
            )
            cmd.extend(["--cov", cov_target, "--cov-report", "term-missing"])

        if project_root:
            cmd.extend(["--rootdir", str(project_root), "-c", "/dev/null"])

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
            output = proc.stdout + "\n" + proc.stderr
            exit_code = proc.returncode
        except subprocess.TimeoutExpired:
            output = "Test execution timed out after 120s"
            exit_code = 1
        except Exception as exc:
            output = str(exc)
            exit_code = 1
    else:
        test_cmd = get_test_command_for_file(str(test_file), language=language)
        if not test_cmd:
            return None, "No test command resolved for this language"

        try:
            proc = subprocess.run(
                test_cmd,
                shell=True,
                capture_output=True,
                text=True,
                timeout=120,
                env=env,
                start_new_session=True,
                stdin=subprocess.DEVNULL,
            )
            output = proc.stdout + "\n" + proc.stderr
            exit_code = proc.returncode
        except subprocess.TimeoutExpired:
            output = "Test execution timed out after 120s"
            exit_code = 1
        except Exception as exc:
            output = str(exc)
            exit_code = 1

    passed, failed, coverage = _parse_test_output(output, language)

    test_hash = (
        calculate_sha256(str(test_file))
        if Path(test_file).exists()
        else None
    )

    report = RunReport(
        timestamp=datetime.datetime.now().isoformat(),
        exit_code=exit_code,
        tests_passed=passed,
        tests_failed=failed,
        coverage=coverage,
        test_hash=test_hash,
    )

    report_data = (
        report.__dict__
        if hasattr(report, "__dict__") and not hasattr(report, "__dataclass_fields__")
        else asdict(report)
    )

    if atomic_state is not None:
        atomic_state.set_run_report(report_data)
    else:
        save_run_report(basename, language, report_data)

    return report, output


# ---------------------------------------------------------------------------
# Helpers – synthetic run reports for agentic success
# ---------------------------------------------------------------------------


def _create_synthetic_run_report_for_agentic_success(
    test_file: str,
    basename: str,
    language: str,
    *,
    atomic_state: Optional[AtomicStateUpdate] = None,
) -> RunReport:
    """Create a synthetic ``RunReport`` when agentic test generation succeeds."""
    test_hash = (
        calculate_sha256(str(test_file))
        if Path(test_file).exists()
        else "agentic_test_success"
    )
    report = RunReport(
        timestamp=datetime.datetime.now().isoformat(),
        exit_code=0,
        tests_passed=1,
        tests_failed=0,
        coverage=0.0,
        test_hash=test_hash,
    )
    report_data = (
        report.__dict__
        if hasattr(report, "__dict__") and not hasattr(report, "__dataclass_fields__")
        else asdict(report)
    )
    if atomic_state is not None:
        atomic_state.set_run_report(report_data)
    else:
        save_run_report(basename, language, report_data)
    return report


# ---------------------------------------------------------------------------
# Helpers – language / agentic detection
# ---------------------------------------------------------------------------


def _use_agentic_path(language: str, agentic_mode: bool) -> bool:
    """Return ``True`` if we should use the agentic path (non-Python **or**
    ``agentic_mode`` explicitly requested for Python)."""
    if agentic_mode:
        return True
    return language.lower() != "python"


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
# Helpers – confirmation callback
# ---------------------------------------------------------------------------


def _get_confirm_callback(
    user_confirmed_overwrite: list,
    app_ref: list,
    headless: bool,
) -> Callable:
    """Return a confirmation callback that auto-confirms after first accept."""

    def _callback(filename: str, message: str) -> bool:
        if user_confirmed_overwrite[0]:
            return True
        if headless:
            try:
                result = click.confirm(message, default=True)
            except Exception:
                result = True
        else:
            if app_ref and app_ref[0] is not None:
                try:
                    result = app_ref[0].request_confirmation(message)
                except Exception:
                    result = True
            else:
                result = True
        if result:
            user_confirmed_overwrite[0] = True
        return result

    return _callback


# ---------------------------------------------------------------------------
# Helpers – result dict construction
# ---------------------------------------------------------------------------


def _build_final_state(pdd_files: Dict[str, Any]) -> Dict[str, Any]:
    state: Dict[str, Any] = {}
    for key in ("prompt", "code", "example", "test"):
        p = pdd_files.get(key)
        if p:
            state[key] = {"exists": Path(p).exists(), "path": str(p)}
        else:
            state[key] = {"exists": False, "path": None}
    return state


def _make_result(
    success: bool,
    operations_completed: List[str],
    skipped_operations: List[str],
    total_cost: float,
    total_time: float,
    final_state: Dict[str, Any],
    errors: List[str],
    model_name: str,
    log_entries: Optional[List[dict]] = None,
) -> Dict[str, Any]:
    result: Dict[str, Any] = {
        "success": success,
        "operations_completed": list(operations_completed),
        "skipped_operations": list(skipped_operations),
        "total_cost": total_cost,
        "total_time": total_time,
        "final_state": final_state,
        "errors": list(errors),
        "error": "; ".join(errors) if errors else None,
        "model_name": model_name,
    }
    if log_entries is not None:
        result["log_entries"] = log_entries
    return result


# ---------------------------------------------------------------------------
# Helpers – dry-run log display
# ---------------------------------------------------------------------------


def _display_sync_log(
    basename: str, language: str, verbose: bool
) -> List[dict]:
    """Load and display sync log entries.  Returns the raw entries."""
    entries = load_operation_log(basename, language)
    if not entries:
        click.echo(f"No sync log found for {basename}_{language.lower()}.")
        return []

    for entry in entries:
        ts = entry.get("timestamp", "?")
        op = entry.get("operation", "?")
        reason = entry.get("reason", "")
        success = entry.get("success")
        cost = entry.get("actual_cost", entry.get("estimated_cost", 0))

        status = "✓" if success else ("✗" if success is False else "…")
        line = f"  [{ts}] {status} {op}"
        if reason:
            line += f" – {reason}"
        if cost:
            line += f"  (${cost:.4f})"
        if verbose:
            dtype = entry.get("decision_type", "")
            conf = entry.get("confidence")
            if dtype:
                line += f"  type={dtype}"
            if conf is not None:
                line += f"  confidence={conf:.2f}"
        click.echo(line)
    return entries


# ---------------------------------------------------------------------------
# Helpers – cycle detection
# ---------------------------------------------------------------------------


def _check_cycle_break(
    operations_completed: List[str], operation: str
) -> Optional[str]:
    """Return a skip-reason string if a cycle/repetition limit is hit,
    else ``None``."""
    recent = operations_completed[-6:]
    op = operation

    # auto-deps: 2+ in last 3 → force generate
    if op == "auto-deps":
        last3 = operations_completed[-3:]
        if last3.count("auto-deps") >= 2:
            return "auto-deps repeated; advancing to generate"

    # Consecutive identical operations
    consec = 0
    for past_op in reversed(operations_completed):
        if past_op == op:
            consec += 1
        else:
            break

    if op == "fix" and consec >= 5:
        return "consecutive fix limit (5) reached"
    if op == "test" and consec >= MAX_CONSECUTIVE_TESTS:
        return f"consecutive test limit ({MAX_CONSECUTIVE_TESTS}) reached"
    if op == "test_extend" and consec >= MAX_TEST_EXTEND_ATTEMPTS:
        return f"test_extend limit ({MAX_TEST_EXTEND_ATTEMPTS}) reached; accepting coverage"
    if op == "crash" and consec >= MAX_CONSECUTIVE_CRASHES:
        return f"consecutive crash limit ({MAX_CONSECUTIVE_CRASHES}) reached"

    # Crash-verify alternation
    MAX_CYCLE_REPEATS = 2
    if len(recent) >= 4 and op in ("crash", "verify"):
        pattern = recent[-4:]
        if (
            pattern == ["crash", "verify", "crash", "verify"]
            or pattern == ["verify", "crash", "verify", "crash"]
        ):
            return "crash↔verify cycle detected"

    # Test-fix alternation
    if len(recent) >= 4 and op in ("test", "fix"):
        pattern = recent[-4:]
        if (
            pattern == ["test", "fix", "test", "fix"]
            or pattern == ["fix", "test", "fix", "test"]
        ):
            return "test↔fix cycle detected"

    return None


# ---------------------------------------------------------------------------
# Main worker logic
# ---------------------------------------------------------------------------


def sync_worker_logic(  # noqa: C901 – complexity is inherent
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
    # TUI mutable refs
    function_name_ref: list,
    cost_ref: list,
    stop_event: threading.Event,
    prompt_color_ref: list,
    code_color_ref: list,
    example_color_ref: list,
    test_color_ref: list,
    prompt_path_ref: list,
    code_path_ref: list,
    example_path_ref: list,
    test_path_ref: list,
    app_ref: list,
    user_confirmed_overwrite: list,
    progress_callback_ref: list,
) -> Dict[str, Any]:
    """Execute the sync workflow loop.  Designed to run inside a worker thread
    (via :class:`SyncApp`) or directly in headless mode."""

    start_time = time.monotonic()
    total_cost: float = 0.0
    last_model = ""
    operations_completed: List[str] = []
    skipped_operations: List[str] = []
    errors: List[str] = []

    # ---- resolve file paths -------------------------------------------------
    try:
        pdd_files = get_pdd_file_paths(
            basename, language, prompts_dir, code_dir, examples_dir, tests_dir
        )
    except FileNotFoundError as exc:
        exc_msg = str(exc)
        # Missing test files are tolerable – they will be generated
        if "test" in exc_msg.lower():
            prompt_path = Path(prompts_dir) / f"{basename}_{language}.prompt"
            # Case-insensitive fallback
            if not prompt_path.exists():
                pdir = Path(prompts_dir)
                if pdir.is_dir():
                    for child in pdir.iterdir():
                        if child.name.lower() == prompt_path.name.lower():
                            prompt_path = child
                            break
            pdd_files = {
                "prompt": str(prompt_path),
                "code": str(Path(code_dir) / f"{basename}.{ext}"),
                "example": str(
                    Path(examples_dir) / f"{basename}_example.{ext}"
                ),
                "test": str(Path(tests_dir) / f"test_{basename}.{ext}"),
            }
        else:
            elapsed = time.monotonic() - start_time
            return _make_result(
                False, operations_completed, skipped_operations,
                total_cost, elapsed, {}, [exc_msg], last_model,
            )
    except Exception as exc:
        elapsed = time.monotonic() - start_time
        return _make_result(
            False, operations_completed, skipped_operations,
            total_cost, elapsed, {}, [str(exc)], last_model,
        )

    test_files_list: Optional[List[str]] = pdd_files.get("test_files")

    # Update TUI refs with initial paths
    _update_file_colors(
        pdd_files,
        prompt_color_ref, code_color_ref, example_color_ref, test_color_ref,
        prompt_path_ref, code_path_ref, example_path_ref, test_path_ref,
    )

    # ---- mock click context -------------------------------------------------
    if confirm_callback is None:
        confirm_callback = _get_confirm_callback(
            user_confirmed_overwrite, app_ref, _is_headless(quiet)
        )

    ctx = _create_mock_context(
        strength=strength,
        temperature=temperature,
        time_param=time_param,
        verbose=verbose,
        quiet=quiet,
        force=force,
        local=local,
        review_examples=review_examples,
        output_cost=output_cost,
        context_override=context_override,
        confirm_callback=confirm_callback,
    )

    prompt_path = pdd_files["prompt"]
    code_path = pdd_files["code"]
    example_path = pdd_files["example"]
    test_path = pdd_files["test"]

    # ---- acquire lock -------------------------------------------------------
    lock = SyncLock(basename, language)
    try:
        lock.__enter__()
    except Exception as exc:
        elapsed = time.monotonic() - start_time
        return _make_result(
            False, operations_completed, skipped_operations,
            total_cost, elapsed, _build_final_state(pdd_files),
            [f"Lock acquisition failed: {exc}"], last_model,
        )
    log_event(basename, language, "lock_acquired", {}, invocation_mode="sync")

    try:
        # ================================================================
        # MAIN WORKFLOW LOOP
        # ================================================================
        while not stop_event.is_set():
            # -- budget check --------------------------------------------------
            if total_cost >= budget:
                log_event(
                    basename, language, "budget_exhausted",
                    {"total_cost": total_cost, "budget": budget},
                    invocation_mode="sync",
                )
                errors.append(f"Budget exhausted (${total_cost:.2f} >= ${budget:.2f})")
                break

            remaining_budget = budget - total_cost
            if remaining_budget < budget * 0.2:
                log_event(
                    basename, language, "budget_warning",
                    {"remaining": remaining_budget},
                    invocation_mode="sync",
                )

            # -- determine next operation --------------------------------------
            function_name_ref[0] = "analyzing"
            for cref in (prompt_color_ref, code_color_ref, example_color_ref, test_color_ref):
                pass  # keep current colours
            prompt_color_ref[0] = COLOR_BLUE

            decision: SyncDecision = sync_determine_operation(
                basename, language, target_coverage
            )
            operation = decision.operation

            # -- terminal states -----------------------------------------------
            if operation in TERMINAL_STATES:
                entry = create_log_entry(
                    operation=operation,
                    reason=decision.reason,
                    invocation_mode="sync",
                    estimated_cost=0,
                    confidence=decision.confidence,
                    decision_type=decision.decision_type,
                )
                update_log_entry(entry, success=True, cost=0, model="", duration=0, error=None)
                append_log_entry(basename, language, entry)
                if operation in ("fail_and_request_manual_merge", "error"):
                    errors.append(decision.reason)
                break

            # -- cycle detection -----------------------------------------------
            cycle_reason = _check_cycle_break(operations_completed, operation)
            if cycle_reason:
                log_event(
                    basename, language, "cycle_break",
                    {"operation": operation, "reason": cycle_reason},
                    invocation_mode="sync",
                )
                errors.append(f"Cycle detected: {cycle_reason}")
                break

            # -- interactive steering ------------------------------------------
            if not no_steer and not _is_headless(quiet):
                steered_op, should_abort = maybe_steer_operation(
                    operation,
                    decision.reason,
                    app_ref,
                    quiet,
                    skip_tests,
                    skip_verify,
                    timeout_s=steer_timeout,
                )
                if should_abort:
                    errors.append("Sync aborted by user steering")
                    log_event(
                        basename, language, "steering_abort", {},
                        invocation_mode="sync",
                    )
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
                        reason=f"Steered from {decision.operation}: {decision.reason}",
                        estimated_cost=decision.estimated_cost,
                        confidence=decision.confidence,
                        decision_type="steering",
                    )

            # -- skip handling -------------------------------------------------
            if operation == "verify" and (skip_verify or skip_tests):
                skipped_operations.append("verify")
                save_fingerprint(
                    basename=basename, language=language,
                    operation="skip:verify",
                    paths={k: Path(v) for k, v in pdd_files.items() if isinstance(v, str)},
                    cost=0, model="",
                )
                entry = create_log_entry(
                    operation="verify", reason="skipped (--skip-verify/--skip-tests)",
                    invocation_mode="sync", estimated_cost=0,
                    confidence=1.0, decision_type="skip",
                )
                update_log_entry(entry, success=True, cost=0, model="", duration=0, error=None)
                append_log_entry(basename, language, entry)
                continue

            if operation in ("test", "test_extend", "fix") and skip_tests:
                skipped_operations.append(operation)
                save_fingerprint(
                    basename=basename, language=language,
                    operation=f"skip:{operation}",
                    paths={k: Path(v) for k, v in pdd_files.items() if isinstance(v, str)},
                    cost=0, model="",
                )
                entry = create_log_entry(
                    operation=operation, reason="skipped (--skip-tests)",
                    invocation_mode="sync", estimated_cost=0,
                    confidence=1.0, decision_type="skip",
                )
                update_log_entry(entry, success=True, cost=0, model="", duration=0, error=None)
                append_log_entry(basename, language, entry)
                continue

            if operation == "crash" and skip_tests:
                skipped_operations.append("crash")
                # Synthetic run_report to prevent infinite loop
                synth = RunReport(
                    timestamp=datetime.datetime.now().isoformat(),
                    exit_code=0, tests_passed=0, tests_failed=0,
                    coverage=0.0, test_hash=None,
                )
                save_run_report(
                    basename, language,
                    synth.__dict__ if hasattr(synth, "__dict__") else asdict(synth),
                )
                save_fingerprint(
                    basename=basename, language=language,
                    operation="skip:crash",
                    paths={k: Path(v) for k, v in pdd_files.items() if isinstance(v, str)},
                    cost=0, model="",
                )
                entry = create_log_entry(
                    operation="crash", reason="skipped (--skip-tests cascading)",
                    invocation_mode="sync", estimated_cost=0,
                    confidence=1.0, decision_type="skip",
                )
                update_log_entry(entry, success=True, cost=0, model="", duration=0, error=None)
                append_log_entry(basename, language, entry)
                continue

            # -- prepare log entry & TUI --------------------------------------
            function_name_ref[0] = operation
            cost_ref[0] = total_cost
            _set_active_color(
                operation,
                prompt_color_ref, code_color_ref, example_color_ref, test_color_ref,
            )

            entry = create_log_entry(
                operation=decision.operation,
                reason=decision.reason,
                invocation_mode="sync",
                estimated_cost=decision.estimated_cost,
                confidence=decision.confidence,
                decision_type=decision.decision_type,
            )

            op_start = time.monotonic()
            op_cost = 0.0
            op_model = ""
            op_success = False
            op_error: Optional[str] = None

            # ================================================================
            # OPERATION DISPATCH
            # ================================================================
            try:
                if operation == "auto-deps":
                    import shutil

                    deps_dir = examples_dir
                    glob_pattern = f"{deps_dir}/**/*.{ext}"
                    csv_path = os.environ.get(
                        "PDD_AUTO_DEPS_CSV_PATH", "project_dependencies.csv"
                    )
                    result = auto_deps_main(
                        ctx=ctx,
                        prompt_file=str(prompt_path),
                        directory_path=glob_pattern,
                        auto_deps_csv_path=csv_path,
                        output=str(prompt_path),
                        force_scan=False,
                    )
                    # result = (modified_prompt, cost, model)
                    op_cost = result[1]
                    op_model = result[2]
                    op_success = True

                elif operation == "generate":
                    clear_run_report(basename, language)

                    result = code_generator_main(
                        ctx=ctx,
                        prompt_file=str(prompt_path),
                        output=str(code_path),
                        original_prompt_file_path=None,
                        force_incremental_flag=False,
                    )
                    # result = (code, incremental, cost, model)
                    op_cost = result[2]
                    op_model = result[3]
                    op_success = True

                elif operation == "example":
                    result = context_generator_main(
                        ctx=ctx,
                        prompt_file=str(prompt_path),
                        code_file=str(code_path),
                        output=str(example_path),
                    )
                    # result = (generated_code, cost, model)
                    op_cost = result[1]
                    op_model = result[2]
                    op_success = True

                elif operation == "crash":
                    agentic = _use_agentic_path(language, agentic_mode)

                    if not agentic and language.lower() == "python":
                        # Python: detect crash by running example
                        ok, stdout, stderr = _run_example_with_error_detection(
                            str(example_path), str(code_path), language
                        )
                        if ok:
                            # No crash – create synthetic success report
                            synth = RunReport(
                                timestamp=datetime.datetime.now().isoformat(),
                                exit_code=0, tests_passed=0, tests_failed=0,
                                coverage=0.0, test_hash=None,
                            )
                            save_run_report(
                                basename, language,
                                synth.__dict__ if hasattr(synth, "__dict__") else asdict(synth),
                            )
                            op_success = True
                            operations_completed.append(operation)
                            _update_file_colors(
                                pdd_files,
                                prompt_color_ref, code_color_ref, example_color_ref, test_color_ref,
                                prompt_path_ref, code_path_ref, example_path_ref, test_path_ref,
                            )
                            continue

                        # Try auto-fix before expensive calls
                        combined_err = stdout + "\n" + stderr
                        if _try_auto_fix_import_error(combined_err, str(code_path), str(example_path)):
                            ok2, _, _ = _run_example_with_error_detection(
                                str(example_path), str(code_path), language
                            )
                            if ok2:
                                op_success = True
                                operations_completed.append(operation)
                                continue

                        # Write error file for crash_main
                        err_file = Path.cwd() / PDD_DIR / "crash_errors.log"
                        err_file.parent.mkdir(parents=True, exist_ok=True)
                        err_file.write_text(combined_err, encoding="utf-8")

                        result = crash_main(
                            ctx=ctx,
                            prompt_file=str(prompt_path),
                            code_file=str(code_path),
                            program_file=str(example_path),
                            error_file=str(err_file),
                            output=str(code_path),
                            output_program=str(example_path),
                            loop=True,
                            strength=strength,
                            temperature=temperature,
                            budget=remaining_budget,
                            max_attempts=max_attempts,
                        )
                        # result = (success, final_code, final_program, attempts, cost, model)
                        op_success = result[0]
                        op_cost = result[4]
                        op_model = result[5]

                        # Re-run example to verify
                        if op_success:
                            v_ok, v_out, v_err = _run_example_with_error_detection(
                                str(example_path), str(code_path), language
                            )
                            rr = RunReport(
                                timestamp=datetime.datetime.now().isoformat(),
                                exit_code=0 if v_ok else 1,
                                tests_passed=0, tests_failed=0,
                                coverage=0.0, test_hash=None,
                            )
                            save_run_report(
                                basename, language,
                                rr.__dict__ if hasattr(rr, "__dict__") else asdict(rr),
                            )
                    else:
                        # Non-Python / agentic: delegate to crash_main with max_attempts=0
                        err_file = Path.cwd() / PDD_DIR / "crash_errors.log"
                        err_file.parent.mkdir(parents=True, exist_ok=True)
                        err_file.write_text(
                            "Non-Python crash detection delegated to agentic handler",
                            encoding="utf-8",
                        )

                        result = crash_main(
                            ctx=ctx,
                            prompt_file=str(prompt_path),
                            code_file=str(code_path),
                            program_file=str(example_path),
                            error_file=str(err_file),
                            output=str(code_path),
                            output_program=str(example_path),
                            loop=True,
                            strength=strength,
                            temperature=temperature,
                            budget=remaining_budget,
                            max_attempts=0,
                        )
                        op_success = result[0]
                        op_cost = result[4]
                        op_model = result[5]

                        # Trust agentic result – save synthetic report
                        if op_success:
                            synth = RunReport(
                                timestamp=datetime.datetime.now().isoformat(),
                                exit_code=0, tests_passed=0, tests_failed=0,
                                coverage=0.0, test_hash=None,
                            )
                            save_run_report(
                                basename, language,
                                synth.__dict__ if hasattr(synth, "__dict__") else asdict(synth),
                            )

                elif operation == "verify":
                    agentic = _use_agentic_path(language, agentic_mode)
                    attempts_for_verify = 0 if agentic else max_attempts

                    result = fix_verification_main(
                        ctx=ctx,
                        prompt_file=str(prompt_path),
                        code_file=str(code_path),
                        program_file=str(example_path),
                        output_results=None,
                        output_code=str(code_path),
                        output_program=str(example_path),
                        loop=True,
                        verification_program=None,
                        max_attempts=attempts_for_verify,
                        budget=remaining_budget,
                        agentic_fallback=True,
                    )
                    # result = (success, final_prog, final_code, attempts, cost, model)
                    op_success = result[0]
                    op_cost = result[4]
                    op_model = result[5]

                elif operation == "test":
                    result = cmd_test_main(
                        ctx=ctx,
                        prompt_file=str(prompt_path),
                        code_file=str(code_path),
                        output=str(test_path),
                        language=language,
                        coverage_report=None,
                        existing_tests=None,
                        target_coverage=None,
                        merge=False,
                        strength=strength,
                        temperature=temperature,
                    )
                    # result = (unit_test_code, cost, model, agentic_success)
                    op_cost = result[1]
                    op_model = result[2]
                    agentic_success = result[3]

                    if agentic_success is True:
                        _create_synthetic_run_report_for_agentic_success(
                            str(test_path), basename, language,
                        )
                        op_success = True
                    elif Path(test_path).exists():
                        rpt, _ = _execute_tests_and_create_run_report(
                            str(test_path), basename, language,
                            target_coverage, code_file=str(code_path),
                            test_files=test_files_list,
                        )
                        op_success = rpt is not None
                    else:
                        op_success = False
                        op_error = "Test file was not created"

                elif operation == "test_extend":
                    # Non-Python (except typescript): skip test_extend entirely
                    lang_lower = language.lower()
                    if lang_lower not in ("python", "typescript"):
                        skipped_operations.append(operation)
                        entry_skip = create_log_entry(
                            operation=operation,
                            reason="skipped for non-Python/TS language",
                            invocation_mode="sync", estimated_cost=0,
                            confidence=1.0, decision_type="skip",
                        )
                        update_log_entry(entry_skip, success=True, cost=0, model="", duration=0, error=None)
                        append_log_entry(basename, language, entry_skip)
                        continue

                    # Read existing run report for coverage info
                    existing_report = read_run_report(basename, language)
                    coverage_rpt_path = None
                    if existing_report:
                        # Write coverage data to temp file for cmd_test_main
                        cov_file = Path.cwd() / PDD_DIR / f"{_safe_basename(basename)}_{lang_lower}_coverage.xml"
                        if cov_file.exists():
                            coverage_rpt_path = str(cov_file)

                    existing_tests_arg = [str(test_path)]
                    if test_files_list:
                        existing_tests_arg = [str(f) for f in test_files_list]

                    result = cmd_test_main(
                        ctx=ctx,
                        prompt_file=str(prompt_path),
                        code_file=str(code_path),
                        output=str(test_path),
                        language=language,
                        coverage_report=coverage_rpt_path,
                        existing_tests=existing_tests_arg if Path(test_path).exists() else None,
                        target_coverage=target_coverage,
                        merge=True,
                        strength=strength,
                        temperature=temperature,
                    )
                    op_cost = result[1]
                    op_model = result[2]
                    agentic_success = result[3]

                    if agentic_success is True and lang_lower not in ("python", "typescript"):
                        _create_synthetic_run_report_for_agentic_success(
                            str(test_path), basename, language,
                        )
                        op_success = True
                    elif Path(test_path).exists():
                        rpt, _ = _execute_tests_and_create_run_report(
                            str(test_path), basename, language,
                            target_coverage, code_file=str(code_path),
                            test_files=test_files_list,
                        )
                        op_success = rpt is not None
                    else:
                        op_success = False
                        op_error = "Test file was not created after test_extend"

                elif operation == "fix":
                    agentic = _use_agentic_path(language, agentic_mode)
                    fix_max = 0 if agentic else max_attempts

                    # Pre-run tests to get error output (Python)
                    err_file_path = Path.cwd() / PDD_DIR / "test_errors.log"
                    err_file_path.parent.mkdir(parents=True, exist_ok=True)

                    if not agentic and language.lower() == "python":
                        project_root = _find_project_root(str(test_path))
                        env_test = os.environ.copy()
                        for var in ("FORCE_COLOR", "COLUMNS"):
                            env_test.pop(var, None)
                        if project_root:
                            pp = str(project_root)
                            sd = project_root / "src"
                            if sd.is_dir():
                                pp = f"{sd}{os.pathsep}{pp}"
                            env_test["PYTHONPATH"] = pp

                        run_files = (
                            [str(f) for f in test_files_list]
                            if test_files_list
                            else [str(test_path)]
                        )
                        py = detect_host_python_executable()
                        test_cmd_list = [py, "-m", "pytest"] + run_files + ["-v"]
                        if project_root:
                            test_cmd_list.extend(["--rootdir", str(project_root), "-c", "/dev/null"])
                        try:
                            pre_result = subprocess.run(
                                test_cmd_list,
                                capture_output=True, text=True, timeout=120,
                                env=env_test, start_new_session=True,
                                stdin=subprocess.DEVNULL,
                            )
                            err_file_path.write_text(
                                pre_result.stdout + "\n" + pre_result.stderr,
                                encoding="utf-8",
                            )
                        except Exception as exc:
                            err_file_path.write_text(str(exc), encoding="utf-8")
                    else:
                        err_file_path.write_text(
                            "Non-Python fix delegated to agentic handler",
                            encoding="utf-8",
                        )

                    # Determine which test file is failing
                    failing_test = str(test_path)
                    if test_files_list and err_file_path.exists():
                        err_content = err_file_path.read_text(encoding="utf-8")
                        failing = extract_failing_files_from_output(err_content)
                        if failing:
                            failing_test = failing[0]

                    result = fix_main(
                        ctx=ctx,
                        prompt_file=str(prompt_path),
                        code_file=str(code_path),
                        unit_test_file=failing_test,
                        error_file=str(err_file_path),
                        output_test=failing_test,
                        output_code=str(code_path),
                        output_results=None,
                        loop=True,
                        verification_program=str(example_path),
                        max_attempts=fix_max,
                        budget=remaining_budget,
                        auto_submit=False,
                        agentic_fallback=True,
                        strength=None,
                        temperature=None,
                        test_files=test_files_list,
                    )
                    # result = (success, fixed_test, fixed_code, attempts, cost, model)
                    op_success = result[0]
                    op_cost = result[4]
                    op_model = result[5]

                    # Post-fix: re-run tests
                    if op_success:
                        if not agentic and language.lower() == "python":
                            rpt, _ = _execute_tests_and_create_run_report(
                                str(test_path), basename, language,
                                target_coverage, code_file=str(code_path),
                                test_files=test_files_list,
                            )
                        else:
                            # Trust agentic result
                            synth = RunReport(
                                timestamp=datetime.datetime.now().isoformat(),
                                exit_code=0, tests_passed=1, tests_failed=0,
                                coverage=0.0,
                                test_hash=calculate_sha256(str(test_path))
                                if Path(test_path).exists()
                                else None,
                            )
                            save_run_report(
                                basename, language,
                                synth.__dict__ if hasattr(synth, "__dict__") else asdict(synth),
                            )

                elif operation == "update":
                    result = update_main(
                        ctx=ctx,
                        input_prompt_file=str(prompt_path),
                        modified_code_file=str(code_path),
                        input_code_file=None,
                        output=str(prompt_path),
                        use_git=True,
                        simple=False,
                    )
                    # result = (updated_prompt, cost, model)
                    op_cost = result[1]
                    op_model = result[2]
                    op_success = True

                else:
                    op_error = f"Unknown operation: {operation}"
                    op_success = False

            except Exception as exc:
                import traceback

                op_error = str(exc)
                op_success = False
                if verbose:
                    traceback.print_exc()

            # ---- post-operation bookkeeping ---------------------------------
            op_duration = time.monotonic() - op_start
            total_cost += op_cost
            cost_ref[0] = total_cost
            if op_model:
                last_model = op_model

            updated_entry = update_log_entry(
                entry,
                success=op_success,
                cost=op_cost,
                model=op_model,
                duration=op_duration,
                error=op_error,
            )
            append_log_entry(basename, language, updated_entry)

            if op_success:
                operations_completed.append(operation)
                # Save fingerprint
                paths_dict = {
                    k: Path(v)
                    for k, v in pdd_files.items()
                    if isinstance(v, str)
                }
                with AtomicStateUpdate(basename, language) as atomic:
                    atomic.set_fingerprint(
                        operation=operation,
                        paths=paths_dict,
                        cost=op_cost,
                        model=op_model,
                    )
            else:
                if op_error:
                    errors.append(f"{operation}: {op_error}")
                operations_completed.append(operation)

            # Refresh file colours
            _update_file_colors(
                pdd_files,
                prompt_color_ref, code_color_ref, example_color_ref, test_color_ref,
                prompt_path_ref, code_path_ref, example_path_ref, test_path_ref,
            )

    finally:
        # ---- release lock ---------------------------------------------------
        try:
            lock.__exit__(None, None, None)
            log_event(
                basename, language, "lock_released", {},
                invocation_mode="sync",
            )
        except Exception:
            pass

    # ---- build result -------------------------------------------------------
    elapsed = time.monotonic() - start_time
    overall_success = (
        len(errors) == 0
        or (operations_completed and operations_completed[-1] == "all_synced")
    )
    # Check if last determine_operation was all_synced
    if not errors:
        overall_success = True

    function_name_ref[0] = "done" if overall_success else "failed"
    stop_event.set()

    return _make_result(
        overall_success,
        operations_completed,
        skipped_operations,
        total_cost,
        elapsed,
        _build_final_state(pdd_files),
        errors,
        last_model,
    )


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
    """Orchestrate the complete PDD sync workflow.

    Coordinates operation execution determined by
    :func:`sync_determine_operation` while providing real-time visual
    feedback via the Textual-based TUI.
    """

    # -- defense in depth: replace None with defaults -------------------------
    if target_coverage is None:
        target_coverage = 90.0
    if budget is None:
        budget = 10.0
    if max_attempts is None:
        max_attempts = 3

    # -- resolve file extension -----------------------------------------------
    from .get_extension import get_extension

    ext = get_extension(language)

    # -- dry-run mode ---------------------------------------------------------
    if dry_run:
        log_entries = _display_sync_log(basename, language, verbose)
        # Also show what would happen next
        decision = sync_determine_operation(
            basename, language, target_coverage, log_mode=True
        )
        click.echo(f"\nNext operation: {decision.operation}")
        click.echo(f"Reason: {decision.reason}")
        if verbose:
            click.echo(f"Decision type: {decision.decision_type}")
            click.echo(f"Confidence: {decision.confidence}")
            click.echo(f"Estimated cost: ${decision.estimated_cost:.4f}")

        return _make_result(
            success=True,
            operations_completed=[],
            skipped_operations=[],
            total_cost=0.0,
            total_time=0.0,
            final_state={},
            errors=[],
            model_name="",
            log_entries=log_entries,
        )

    # -- TUI mutable references -----------------------------------------------
    function_name_ref = ["initializing"]
    cost_ref = [0.0]
    stop_event = threading.Event()
    prompt_color_ref = [COLOR_BLUE]
    code_color_ref = [COLOR_RED]
    example_color_ref = [COLOR_RED]
    test_color_ref = [COLOR_RED]
    prompt_path_ref = [""]
    code_path_ref = [""]
    example_path_ref = [""]
    test_path_ref = [""]
    app_ref: list = [None]
    user_confirmed_overwrite = [force]
    progress_callback_ref: list = [None]

    worker_kwargs = dict(
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
        stop_event=stop_event,
        prompt_color_ref=prompt_color_ref,
        code_color_ref=code_color_ref,
        example_color_ref=example_color_ref,
        test_color_ref=test_color_ref,
        prompt_path_ref=prompt_path_ref,
        code_path_ref=code_path_ref,
        example_path_ref=example_path_ref,
        test_path_ref=test_path_ref,
        app_ref=app_ref,
        user_confirmed_overwrite=user_confirmed_overwrite,
        progress_callback_ref=progress_callback_ref,
    )

    headless = _is_headless(quiet)

    # -- headless mode --------------------------------------------------------
    if headless:
        os.environ["PDD_FORCE"] = "1"

        if confirm_callback is None:
            worker_kwargs["confirm_callback"] = _get_confirm_callback(
                user_confirmed_overwrite, app_ref, True
            )

        result = sync_worker_logic(**worker_kwargs)
        return result

    # -- TUI mode -------------------------------------------------------------
    def _worker_func() -> Dict[str, Any]:
        return sync_worker_logic(**worker_kwargs)

    app = SyncApp(worker_func=_worker_func)
    app_ref[0] = app

    app_result = app.run()

    # Check for worker thread crash
    if hasattr(app, "worker_exception") and app.worker_exception is not None:
        import traceback as tb_mod

        print(
            f"Sync worker crashed: {app.worker_exception}",
            file=sys.stderr,
        )
        tb_mod.print_exception(
            type(app.worker_exception),
            app.worker_exception,
            app.worker_exception.__traceback__,
            file=sys.stderr,
        )
        return _make_result(
            success=False,
            operations_completed=[],
            skipped_operations=[],
            total_cost=cost_ref[0],
            total_time=0.0,
            final_state={},
            errors=[str(app.worker_exception)],
            model_name="",
        )

    if app_result is None:
        return _make_result(
            success=False,
            operations_completed=[],
            skipped_operations=[],
            total_cost=cost_ref[0],
            total_time=0.0,
            final_state={},
            errors=["Sync was interrupted"],
            model_name="",
        )

    # -- exit animation -------------------------------------------------------
    if not quiet:
        from .sync_tui import show_exit_animation

        success = app_result.get("success", False) if isinstance(app_result, dict) else False
        show_exit_animation(
            success=success,
            operations=app_result.get("operations_completed", [])
            if isinstance(app_result, dict)
            else [],
            total_cost=app_result.get("total_cost", 0.0)
            if isinstance(app_result, dict)
            else 0.0,
            total_time=app_result.get("total_time", 0.0)
            if isinstance(app_result, dict)
            else 0.0,
        )

    return app_result if isinstance(app_result, dict) else _make_result(
        success=False,
        operations_completed=[],
        skipped_operations=[],
        total_cost=0.0,
        total_time=0.0,
        final_state={},
        errors=["Unexpected TUI result"],
        model_name="",
    )