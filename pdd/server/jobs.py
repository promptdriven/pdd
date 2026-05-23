from __future__ import annotations

import asyncio
import logging
import os
import signal
import subprocess
import sys
import re
import threading
import time
from concurrent.futures import ThreadPoolExecutor
from dataclasses import dataclass, field
from datetime import datetime, timezone
from pathlib import Path
from typing import Any, Awaitable, Callable, Dict, List, Optional
from uuid import uuid4

# Robust import for rich console
try:
    from rich.console import Console
    console = Console()
except ImportError:
    class Console:
        def print(self, *args, **kwargs):
            import builtins
            builtins.print(*args)
    console = Console()

# Robust import for internal dependencies
try:
    from .click_executor import ClickCommandExecutor, get_pdd_command
except ImportError:
    class ClickCommandExecutor:
        def __init__(self, base_context_obj=None, output_callback=None):
            pass
        def execute(self, *args, **kwargs):
            raise NotImplementedError("ClickCommandExecutor not available")

    def get_pdd_command(name):
        return None

from .models import BudgetSettings, JobStatus

try:
    from .budget_settings import (
        BudgetStore,
        effective_cap as _effective_cap_fn,
        pdd_issue_defaults,
        validate_amount,
    )
    from ..cost_budget_watcher import watch as _watch_csv
except ImportError:  # pragma: no cover - support partial installs
    BudgetStore = None  # type: ignore[assignment]
    _effective_cap_fn = None  # type: ignore[assignment]
    pdd_issue_defaults = None  # type: ignore[assignment]
    validate_amount = None  # type: ignore[assignment]
    _watch_csv = None  # type: ignore[assignment]


# Maximum time (seconds) a subprocess job may run before being killed
JOB_TIMEOUT = 1800

# Nested PDD subprocess commands an autonomous `pdd-issue` run may spawn.
# Used to build the cost-CSV `commands` filter for the budget watcher;
# filtering on `{"issue"}` would sum to $0 because the issue command itself
# never writes a track_cost row — it dispatches into these subcommands.
PDD_ISSUE_NESTED_COMMANDS = frozenset(
    {
        "change",
        "sync",
        "bug",
        "fix",
        "generate",
        "test",
        "example",
        "update",
        "verify",
        "split",
        "detect",
        "auto-deps",
        "conflicts",
        "preprocess",
        "crash",
    }
)

# Sentinel for `update_budget` keyword arguments: distinguishes "not provided"
# from "explicitly set to None". `None` semantically means "clear this field".
_UNSET = object()


def _coerce_node_count_strict(value: Any) -> int:
    """Reject fractional inputs (3.9 -> error, not silent truncation to 3).

    Mirrors the BudgetUpdateRequest field validator so programmatic callers
    of JobManager.update_budget / update_node_count get the same strictness
    as REST callers. bool is rejected even though it subclasses int.
    """
    if isinstance(value, bool):
        raise ValueError(f"node_count must be an integer: {value!r}")
    if isinstance(value, int):
        coerced = value
    elif isinstance(value, float):
        if not value.is_integer():
            raise ValueError(
                f"node_count must be an integer, not a fractional number: {value!r}"
            )
        coerced = int(value)
    elif isinstance(value, str):
        stripped = value.strip()
        if not stripped:
            raise ValueError("Empty node_count")
        try:
            coerced = int(stripped)
        except ValueError as exc:
            raise ValueError(
                f"node_count must be an integer string, not {value!r}"
            ) from exc
    else:
        raise ValueError(
            f"node_count must be int or int-string, got {type(value).__name__}"
        )
    if coerced < 0:
        raise ValueError(f"node_count must be >= 0: {value!r}")
    if coerced > 10000:
        raise ValueError(f"node_count {coerced} exceeds the hard ceiling 10000")
    return coerced

# Once a job reaches one of these statuses, subsequent handlers must NOT
# overwrite the status field — a later assignment would lose information
# (most importantly: BUDGET_EXCEEDED set by _handle_budget_exceeded must
# not be demoted to CANCELLED by the racing _execute_job CancelledError
# handler).
_TERMINAL_STATUSES = frozenset(
    {
        JobStatus.COMPLETED,
        JobStatus.FAILED,
        JobStatus.CANCELLED,
        JobStatus.BUDGET_EXCEEDED,
    }
)

# Global options that must be placed BEFORE the subcommand (defined on cli group)
GLOBAL_OPTIONS = {
    "force", "strength", "temperature", "time", "verbose", "quiet",
    "output_cost", "review_examples", "local", "context", "list_contexts", "core_dump"
}

# Commands where specific args should be positional (not --options)
POSITIONAL_ARGS = {
    "sync": ["basename"],
    "generate": ["prompt_file"],
    "test": ["prompt_file", "code_file"],
    "example": ["prompt_file", "code_file"],
    "fix": ["args"],  # Always uses variadic "args" (both agentic and manual modes)
    "bug": ["args"],
    "update": ["args"],
    "crash": ["prompt_file", "code_file", "program_file", "error_file"],
    "verify": ["prompt_file", "code_file", "verification_program"],
    # pdd split TARGET_FILE (agentic default, matches routes/commands.py).
    # Legacy mode (--legacy with 3 positional args) is not exposed through the
    # frontend/job queue; it must be invoked directly via the CLI.
    "split": ["target_file"],
    "change": ["args"],  # Always uses variadic "args" (both agentic and manual modes)
    "detect": ["args"],
    "auto-deps": ["prompt_file", "directory_path"],
    "conflicts": ["prompt_file", "prompt2"],
    "preprocess": ["prompt_file"],
}

# Manual mode file key mappings for fix/change commands
# These commands use variadic "args" for BOTH modes, but the frontend sends semantic keys
# for manual mode which we need to convert to ordered positional arguments
MANUAL_MODE_FILE_KEYS = {
    "fix": ["prompt_file", "code_file", "unit_test_files", "error_file"],
    "change": ["change_prompt_file", "input_code", "input_prompt_file"],
}

logger = logging.getLogger(__name__)


def _extract_architecture_conformance_error(
    stdout_text: str,
    stderr_text: str,
    command: str,
    args: Optional[Dict[str, Any]],
) -> Optional[str]:
    """
    Surface architecture-conformance failure details from subprocess output
    (issue #865). Returns a formatted multi-section error string, or None if
    no conformance markers are present in the output.

    The returned message includes (when available):
      - The structured ``=== architecture conformance failure ===`` block
        verbatim, OR the matching ``Architecture conformance error for ...``
        line plus its surrounding ``Expected:``/``Found:``/``missing`` context.
      - A ``Reproduce locally:`` line preserved verbatim from the runner output
        if present, otherwise constructed as ``Reproduce locally: pdd sync
        <basename>`` from the sync target.
      - The runner's ``--- env ---`` fingerprint block verbatim if present.
    """
    full_output = (stdout_text or "") + "\n" + (stderr_text or "")

    has_structured = "=== architecture conformance failure ===" in full_output
    has_simple = "Architecture conformance error for " in full_output

    if not (has_structured or has_simple):
        return None

    sections: List[str] = []

    # 1) Structured block verbatim, or simple line + context.
    if has_structured:
        match = re.search(
            r"(=== architecture conformance failure ===.*?)"
            r"(?=\n=== |\n\s*\n(?=[^\s])|\Z)",
            full_output,
            re.DOTALL,
        )
        if match:
            sections.append(match.group(1).rstrip())
    elif has_simple:
        lines = full_output.splitlines()
        for idx, line in enumerate(lines):
            if "Architecture conformance error for " in line:
                context: List[str] = [line]
                j = idx + 1
                blank_streak = 0
                while j < len(lines):
                    nxt = lines[j]
                    stripped = nxt.strip()
                    if not stripped:
                        blank_streak += 1
                        if blank_streak >= 2:
                            break
                        context.append(nxt)
                        j += 1
                        continue
                    blank_streak = 0
                    lower = stripped.lower()
                    if (
                        stripped.startswith("Expected:")
                        or stripped.startswith("Found:")
                        or "missing" in lower
                        or nxt.startswith((" ", "\t", "-", "*"))
                    ):
                        context.append(nxt)
                        j += 1
                        continue
                    break
                sections.append("\n".join(context).rstrip())
                break

    # 2) Reproduce locally: line — preserve verbatim if present, else build.
    repro_match = re.search(r"^Reproduce locally:.*$", full_output, re.MULTILINE)
    if repro_match:
        sections.append(repro_match.group(0).rstrip())
    else:
        target: Optional[str] = None
        if isinstance(args, dict) and args:
            for key in ("basename", "target", "target_file", "prompt_file"):
                if key in args and args[key]:
                    target = str(args[key])
                    break
            if target is None:
                # Fallback: first positional argument value for the command.
                pos_names = POSITIONAL_ARGS.get(command, [])
                for pn in pos_names:
                    val = args.get(pn)
                    if val:
                        target = str(val) if not isinstance(val, (list, tuple)) else (
                            str(val[0]) if val else None
                        )
                        if target:
                            break
        if target:
            sections.append(f"Reproduce locally: pdd sync {target}")
        else:
            sections.append("Reproduce locally: pdd sync")

    # 3) --- env --- fingerprint block (verbatim).
    env_match = re.search(
        r"(--- env ---.*?)(?=\n\s*\n(?=[^\s])|\n--- |\Z)",
        full_output,
        re.DOTALL,
    )
    if env_match:
        sections.append(env_match.group(1).rstrip())

    return "\n\n".join(s for s in sections if s)


def _find_pdd_executable() -> Optional[str]:
    """Find the pdd executable path."""
    import shutil

    # First try to find 'pdd' in PATH
    pdd_path = shutil.which("pdd")
    if pdd_path:
        return pdd_path

    # Try to find 'pdd' in the same directory as the Python interpreter
    python_dir = Path(sys.executable).parent
    pdd_in_python_dir = python_dir / "pdd"
    if pdd_in_python_dir.exists():
        return str(pdd_in_python_dir)

    return None


def _build_subprocess_command_args(
    command: str,
    args: Optional[Dict[str, Any]],
    options: Optional[Dict[str, Any]]
) -> List[str]:
    """
    Build command line arguments for pdd subprocess.

    Global options (--force, --strength, etc.) are placed BEFORE the subcommand.
    Command-specific options are placed AFTER the subcommand and positional args.
    """
    pdd_exe = _find_pdd_executable()

    if pdd_exe:
        cmd_args = [pdd_exe]
    else:
        # Fallback: use runpy to run the CLI module
        cmd_args = [
            sys.executable, "-c",
            "import sys; from pdd.cli import cli; sys.exit(cli())"
        ]

    # Separate global options from command-specific options
    global_opts: Dict[str, Any] = {}
    cmd_opts: Dict[str, Any] = {}

    if options:
        for key, value in options.items():
            normalized_key = key.replace("-", "_")
            if normalized_key in GLOBAL_OPTIONS:
                global_opts[key] = value
            else:
                cmd_opts[key] = value

    # Add global options BEFORE the command
    for key, value in global_opts.items():
        if isinstance(value, bool):
            if value:
                cmd_args.append(f"--{key.replace('_', '-')}")
        elif isinstance(value, (list, tuple)):
            for v in value:
                cmd_args.extend([f"--{key.replace('_', '-')}", str(v)])
        elif value is not None:
            cmd_args.extend([f"--{key.replace('_', '-')}", str(value)])

    # Add the command
    cmd_args.append(command)

    # Handle fix/change manual mode: convert semantic file keys to positional args
    # and add --manual flag. Both modes use variadic "args" parameter.
    if command in MANUAL_MODE_FILE_KEYS and args and "args" not in args:
        # Manual mode detected: has file keys but no "args" key
        file_keys = MANUAL_MODE_FILE_KEYS[command]
        # Check if any file keys are present
        if any(k in args for k in file_keys):
            # Convert file keys to ordered positional args list (order matters!)
            positional_values = []
            for key in file_keys:
                if key in args and args[key] is not None:
                    positional_values.append(str(args[key]))
            # Collect remaining args that aren't file keys (e.g., verification_program)
            remaining_args = {k: v for k, v in args.items() if k not in file_keys}
            # Build new args with positional values
            args = {"args": positional_values}
            # Move remaining args to cmd_opts (they should be options like --verification-program)
            for key, value in remaining_args.items():
                cmd_opts[key] = value
            # Add --manual flag to command-specific options
            cmd_opts["manual"] = True

    # Get positional arg names for this command
    positional_names = POSITIONAL_ARGS.get(command, [])

    if args:
        # First, add positional arguments in order
        for pos_name in positional_names:
            if pos_name in args:
                value = args[pos_name]
                if pos_name == "args" and isinstance(value, (list, tuple)):
                    cmd_args.extend(str(v) for v in value)
                elif value is not None:
                    cmd_args.append(str(value))

        # Then, add remaining args as options
        for key, value in args.items():
            if key in positional_names:
                continue
            if isinstance(value, bool):
                if value:
                    cmd_args.append(f"--{key.replace('_', '-')}")
            elif isinstance(value, (list, tuple)):
                for v in value:
                    cmd_args.extend([f"--{key.replace('_', '-')}", str(v)])
            elif value is not None:
                cmd_args.extend([f"--{key.replace('_', '-')}", str(value)])

    # Add command-specific options
    if cmd_opts:
        for key, value in cmd_opts.items():
            if isinstance(value, bool):
                if value:
                    cmd_args.append(f"--{key.replace('_', '-')}")
            elif isinstance(value, (list, tuple)):
                for v in value:
                    cmd_args.extend([f"--{key.replace('_', '-')}", str(v)])
            elif value is not None:
                cmd_args.extend([f"--{key.replace('_', '-')}", str(value)])

    return cmd_args


@dataclass
class Job:
    """
    Internal representation of a queued or executing job.
    """
    id: str = field(default_factory=lambda: str(uuid4()))
    command: str = ""
    args: Dict[str, Any] = field(default_factory=dict)
    options: Dict[str, Any] = field(default_factory=dict)
    status: JobStatus = JobStatus.QUEUED
    result: Optional[Any] = None
    error: Optional[str] = None
    cost: float = 0.0
    created_at: datetime = field(default_factory=lambda: datetime.now(timezone.utc))
    started_at: Optional[datetime] = None
    completed_at: Optional[datetime] = None
    # Live output during execution (updated in real-time)
    live_stdout: str = ""
    live_stderr: str = ""
    # Budget control fields (None until /pdd budget ... or pdd-issue defaults
    # are applied; see pdd/server/budget_settings.py).
    budget_cap: Optional[float] = None
    node_budget: Optional[float] = None
    max_total_cap: Optional[float] = None
    node_count: Optional[int] = None

    def to_dict(self) -> Dict[str, Any]:
        return {
            "id": self.id,
            "command": self.command,
            "args": self.args,
            "options": self.options,
            "status": self.status.value,
            "result": self.result,
            "error": self.error,
            "cost": self.cost,
            "created_at": self.created_at.isoformat(),
            "started_at": self.started_at.isoformat() if self.started_at else None,
            "completed_at": self.completed_at.isoformat() if self.completed_at else None,
            "live_stdout": self.live_stdout,
            "live_stderr": self.live_stderr,
            "budget_cap": self.budget_cap,
            "node_budget": self.node_budget,
            "max_total_cap": self.max_total_cap,
            "node_count": self.node_count,
        }


class JobCallbacks:
    """Async callback handlers for job lifecycle events."""

    def __init__(self):
        self._on_start: List[Callable[[Job], Awaitable[None]]] = []
        self._on_output: List[Callable[[Job, str, str], Awaitable[None]]] = []
        self._on_progress: List[Callable[[Job, int, int, str], Awaitable[None]]] = []
        self._on_complete: List[Callable[[Job], Awaitable[None]]] = []
        self._on_budget_exceeded: List[
            Callable[[str, float, float], Awaitable[None]]
        ] = []

    def on_start(self, callback: Callable[[Job], Awaitable[None]]) -> None:
        self._on_start.append(callback)

    def on_output(self, callback: Callable[[Job, str, str], Awaitable[None]]) -> None:
        self._on_output.append(callback)

    def on_progress(self, callback: Callable[[Job, int, int, str], Awaitable[None]]) -> None:
        self._on_progress.append(callback)

    def on_complete(self, callback: Callable[[Job], Awaitable[None]]) -> None:
        self._on_complete.append(callback)

    def on_budget_exceeded(
        self, callback: Callable[[str, float, float], Awaitable[None]]
    ) -> None:
        """Register a callback invoked once when the cost watcher trips.

        Receives ``(job_id, spent, cap)``.
        """
        self._on_budget_exceeded.append(callback)

    async def emit_start(self, job: Job) -> None:
        for callback in self._on_start:
            try:
                await callback(job)
            except Exception as e:
                console.print(f"[red]Error in on_start callback: {e}[/red]")

    async def emit_output(self, job: Job, stream_type: str, text: str) -> None:
        for callback in self._on_output:
            try:
                await callback(job, stream_type, text)
            except Exception as e:
                console.print(f"[red]Error in on_output callback: {e}[/red]")

    async def emit_progress(self, job: Job, current: int, total: int, message: str = "") -> None:
        for callback in self._on_progress:
            try:
                await callback(job, current, total, message)
            except Exception as e:
                console.print(f"[red]Error in on_progress callback: {e}[/red]")

    async def emit_complete(self, job: Job) -> None:
        for callback in self._on_complete:
            try:
                await callback(job)
            except Exception as e:
                console.print(f"[red]Error in on_complete callback: {e}[/red]")

    async def emit_budget_exceeded(self, job_id: str, spent: float, cap: float) -> None:
        for callback in self._on_budget_exceeded:
            try:
                await callback(job_id, spent, cap)
            except Exception as e:
                console.print(
                    f"[red]Error in on_budget_exceeded callback: {e}[/red]"
                )


class JobManager:
    """
    Manages async job execution, queuing, and lifecycle tracking.
    """

    def __init__(
        self,
        max_concurrent: int = 1,
        executor: Optional[Callable[[Job], Awaitable[Dict[str, Any]]]] = None,
        project_root: Optional[Path] = None,
    ):
        self.max_concurrent = max_concurrent
        self.callbacks = JobCallbacks()
        self.project_root = project_root or Path.cwd()

        self._jobs: Dict[str, Job] = {}
        self._tasks: Dict[str, asyncio.Task] = {}
        self._semaphore = asyncio.Semaphore(max_concurrent)
        self._cancel_events: Dict[str, asyncio.Event] = {}

        # Track running subprocesses for cancellation
        self._processes: Dict[str, subprocess.Popen] = {}
        self._process_lock = threading.Lock()

        self._thread_pool = ThreadPoolExecutor(
            max_workers=max_concurrent,
            thread_name_prefix="pdd_job_worker"
        )

        self._custom_executor = executor

        # Per-job watcher handles (cost_budget_watcher.Watcher) so update_budget
        # and cleanup can reach them. Keyed by job_id.
        self._watchers: Dict[str, Any] = {}
        # Lazy budget settings store; only instantiated when budgets are used,
        # so projects that never touch the GitHub App control surface don't pay
        # for the threading.Lock.
        self._budget_store: Optional["BudgetStore"] = None

    def _ensure_budget_store(self) -> "BudgetStore":
        if BudgetStore is None:
            raise RuntimeError(
                "Budget control modules are unavailable; "
                "pdd/server/budget_settings.py is missing."
            )
        if self._budget_store is None:
            self._budget_store = BudgetStore()
        return self._budget_store

    @staticmethod
    def _commands_filter_for(command: str) -> Optional[frozenset]:
        if command == "issue":
            return PDD_ISSUE_NESTED_COMMANDS
        return frozenset({command})

    def subprocess_env(
        self, job: Job, *, base_env: Optional[Dict[str, str]] = None
    ) -> Dict[str, str]:
        """Build the subprocess environment for ``job``'s spawned children.

        Custom executors (the GitHub App's pdd-issue driver, etc.) MUST
        pass the returned dict as ``env=`` to ``subprocess.Popen`` /
        ``asyncio.create_subprocess_*`` instead of relying on
        ``os.environ``. This makes per-job isolation safe under
        ``max_concurrent > 1``: each spawned child sees its own
        ``PDD_JOB_ID`` and ``PDD_OUTPUT_COST_PATH`` regardless of which
        other jobs the manager is concurrently driving.

        The default-subprocess path (``_run_click_command``) uses this
        helper too, so both code paths share one implementation.
        """
        env = dict(base_env if base_env is not None else os.environ)
        env['PDD_JOB_ID'] = job.id
        per_job_csv = (job.options or {}).get("output_cost")
        if per_job_csv:
            env['PDD_OUTPUT_COST_PATH'] = str(per_job_csv)
        else:
            # No per-job CSV resolved — clear any inherited shared path so
            # the child cannot write to a foreign file we never read.
            env.pop('PDD_OUTPUT_COST_PATH', None)
        return env

    def _resolve_cost_csv_path(self, job: Job) -> Optional[Path]:
        """Resolve the cost-CSV path for this job.

        Two invariants this must enforce:
          1. **Late-budget enforceability**: a job that starts uncapped MUST
             still have a CSV writer so a subsequent `/pdd budget N` can
             enforce against the spend that accumulated during the
             previously-uncapped window. We therefore derive a CSV path
             unconditionally — not only when a cap is set at submit time.
          2. **Per-job isolation**: two jobs of the same command sharing
             one CSV (via either an explicit options.output_cost or a
             process-wide PDD_OUTPUT_COST_PATH) would have their watchers
             count each other's rows, since the watcher filter is
             `command` + `started_at` only. We therefore prefer a
             derived per-job path under `project_root/.pdd/` over any
             shared path so each job's watcher reads only that job's
             rows. The shared path is honoured ONLY when explicitly set
             on `job.options["output_cost"]`; the process-wide env var
             is treated as a default the caller wants to NOT inherit
             across jobs.

        Returns the resolved Path. Returns None only if the parent
        directory cannot be created (logged warning; budget enforcement
        will then be inactive for this job).
        """
        explicit = (job.options or {}).get("output_cost") if job.options else None
        if explicit:
            path = Path(explicit)
            # Resolve relative paths against project_root so the watcher
            # (running in the server's cwd, which may differ from the
            # subprocess cwd) sees the same file the subprocess writes
            # to. Otherwise a caller passing "custom/cost.csv" gets two
            # different files — server-cwd/custom/cost.csv for the
            # watcher and project_root/custom/cost.csv for the
            # subprocess — and spend stays $0.
            if not path.is_absolute():
                base = self.project_root or Path.cwd()
                path = (base / path).resolve()
                # Mutate job.options so the subprocess --output-cost
                # arg also uses the absolute form; no ambiguity for
                # any later reader.
                if job.options is None:
                    job.options = {}
                job.options["output_cost"] = str(path)
            # Ensure the parent directory exists so track_cost can write
            # the first row; the subprocess catches the OSError and
            # swallows it, which would leave the watcher silently
            # stuck at $0. mkdir is idempotent under parents=True.
            try:
                path.parent.mkdir(parents=True, exist_ok=True)
            except OSError as exc:
                console.print(
                    f"[yellow]Could not create cost-CSV parent "
                    f"{path.parent} for job {job.id}: {exc}; "
                    f"track_cost writes may fail silently.[/yellow]"
                )
            return path

        # No explicit per-job path. Derive a per-job default so:
        #   - late /pdd budget can find spend rows accumulated during
        #     the uncapped window
        #   - concurrent same-command jobs do not contaminate each
        #     other's spend
        derived = (self.project_root or Path.cwd()) / ".pdd" / f"cost-{job.id}.csv"
        try:
            derived.parent.mkdir(parents=True, exist_ok=True)
        except OSError as exc:
            console.print(
                f"[yellow]Could not create default cost-CSV directory "
                f"{derived.parent}: {exc}; budget enforcement will be "
                f"inactive for job {job.id}.[/yellow]"
            )
            return None

        if job.options is None:
            job.options = {}
        job.options["output_cost"] = str(derived)
        return derived

    def _start_watcher_for(self, job: Job) -> None:
        """Wire ``cost_budget_watcher`` around a job that has an effective cap."""
        if _watch_csv is None or _effective_cap_fn is None:
            return
        cap = _effective_cap_fn(
            job.command,
            budget_cap=job.budget_cap,
            node_budget=job.node_budget,
            max_total_cap=job.max_total_cap,
            node_count=job.node_count,
        )
        csv_path = self._resolve_cost_csv_path(job)
        if cap is None or csv_path is None:
            return

        loop = asyncio.get_event_loop()
        store = self._ensure_budget_store()
        store.set(
            job.id,
            BudgetSettings(
                command=job.command,
                node_budget=job.node_budget,
                max_total_cap=job.max_total_cap,
                budget_cap=job.budget_cap,
                effective_cap=cap,
                spent_so_far=0.0,
                status=job.status,
                node_count=job.node_count,
            ),
        )

        # Do NOT capture `cap` in this closure: it would freeze the cap to
        # the value at submit time and the budget-exceeded callback would
        # report a stale cap after a mid-run /pdd budget change.
        # _handle_budget_exceeded recomputes the current effective cap
        # from the (potentially updated) job.budget fields when it fires.
        job_id_capture = job.id

        def _on_exceeded(spent: float) -> None:
            asyncio.run_coroutine_threadsafe(
                self._handle_budget_exceeded(job_id_capture, spent), loop
            )

        try:
            self._watchers[job.id] = _watch_csv(
                csv_path,
                cap,
                _on_exceeded,
                commands=self._commands_filter_for(job.command),
                started_at=job.started_at,
                poll_interval=2.0,
                job_id=job.id,
            )
        except Exception as exc:  # noqa: BLE001
            console.print(f"[red]Failed to start budget watcher: {exc}[/red]")

    def _stop_watcher_for(self, job_id: str) -> None:
        watcher = self._watchers.pop(job_id, None)
        if watcher is not None:
            try:
                watcher.stop()
            except Exception:  # noqa: BLE001
                pass

    async def _handle_budget_exceeded(self, job_id: str, spent: float) -> None:
        """Final-status + cancel handler invoked by the watcher's
        on_exceeded callback.

        Recomputes the current effective cap from the (potentially
        updated) job budget fields rather than trusting a captured value,
        so /pdd budget changes during a run are reflected in the
        emitted ``BudgetExceededMessage``.
        """
        job = self._jobs.get(job_id)
        if job is None or job.status not in (JobStatus.QUEUED, JobStatus.RUNNING):
            return
        # CRITICAL: set the terminal status BEFORE calling cancel(), so that
        # the racing _execute_job exception handler (which fires on the
        # asyncio.CancelledError that cancel() injects) sees a terminal
        # status and does not demote BUDGET_EXCEEDED back to CANCELLED. The
        # _execute_job handlers honor `_TERMINAL_STATUSES`; if they don't,
        # there is a race and the wrong final status sticks.
        job.cost = max(job.cost, spent)
        job.status = JobStatus.BUDGET_EXCEEDED
        if not job.completed_at:
            job.completed_at = datetime.now(timezone.utc)

        current_cap = None
        if _effective_cap_fn is not None:
            current_cap = _effective_cap_fn(
                job.command,
                budget_cap=job.budget_cap,
                node_budget=job.node_budget,
                max_total_cap=job.max_total_cap,
                node_count=job.node_count,
            )

        if self._budget_store is not None:
            try:
                self._budget_store.update(
                    job_id,
                    spent_so_far=spent,
                    status=JobStatus.BUDGET_EXCEEDED,
                )
            except KeyError:
                pass
        try:
            await self.cancel(job_id)
        except Exception as exc:  # noqa: BLE001
            console.print(f"[red]Cancel after budget exceeded failed: {exc}[/red]")
        await self.callbacks.emit_budget_exceeded(
            job_id, spent, current_cap if current_cap is not None else spent,
        )

    async def submit(
        self,
        command: str,
        args: Dict[str, Any] = None,
        options: Dict[str, Any] = None,
        *,
        budget_cap: Optional[float] = None,
        node_budget: Optional[float] = None,
        max_total_cap: Optional[float] = None,
    ) -> Job:
        # Validate at the API boundary even when the route's pydantic
        # validation has not run (programmatic callers, tests, GitHub App
        # internal submissions). validate_amount enforces the same > 0 /
        # <= $10000 rule the budget-update path applies, preventing a
        # negative or absurd initial budget_cap from sticking on a job
        # and producing an effective_cap of -1.
        if validate_amount is not None:
            if budget_cap is not None:
                budget_cap = validate_amount(budget_cap)
            if node_budget is not None:
                node_budget = validate_amount(node_budget)
            if max_total_cap is not None:
                max_total_cap = validate_amount(max_total_cap)

        job = Job(
            command=command,
            args=args or {},
            options=options or {},
            budget_cap=budget_cap,
            node_budget=node_budget,
            max_total_cap=max_total_cap,
        )

        self._jobs[job.id] = job
        self._cancel_events[job.id] = asyncio.Event()

        # Resolve and pre-inject a per-job cost CSV path BEFORE the
        # subprocess starts, regardless of whether a cap is currently
        # set. This guarantees:
        #   - a late `/pdd budget` arriving on an initially-uncapped run
        #     has a CSV to read instead of seeing $0 forever, and
        #   - the subprocess writes to a per-job file so concurrent
        #     same-command jobs cannot count each other's spend.
        # Resolution mutates job.options["output_cost"] when the path
        # is derived; the subprocess command builder reads from there
        # to emit --output-cost.
        self._resolve_cost_csv_path(job)

        console.print(f"[blue]Job submitted:[/blue] {job.id} ({command})")

        task = asyncio.create_task(self._execute_wrapper(job))
        self._tasks[job.id] = task

        # Callback to handle cleanup and edge-case cancellation (cancelled before start)
        def _on_task_done(t: asyncio.Task):
            if job.id in self._tasks:
                del self._tasks[job.id]
            
            # If task was cancelled but job status wasn't updated (e.g. never started running)
            if t.cancelled() and job.status == JobStatus.QUEUED:
                job.status = JobStatus.CANCELLED
                if not job.completed_at:
                    job.completed_at = datetime.now(timezone.utc)
                console.print(f"[yellow]Job cancelled (Task Done):[/yellow] {job.id}")

        task.add_done_callback(_on_task_done)

        return job

    async def _execute_wrapper(self, job: Job) -> None:
        try:
            async with self._semaphore:
                await self._execute_job(job)
        except asyncio.CancelledError:
            # Handle cancellation while waiting for semaphore
            if job.status == JobStatus.QUEUED:
                job.status = JobStatus.CANCELLED
                job.completed_at = datetime.now(timezone.utc)
                console.print(f"[yellow]Job cancelled (Queue):[/yellow] {job.id}")
            raise # Re-raise to ensure task is marked as cancelled for the callback

    async def _execute_job(self, job: Job) -> None:
        try:
            # 1. Check cancellation before starting
            if self._cancel_events[job.id].is_set():
                job.status = JobStatus.CANCELLED
                console.print(f"[yellow]Job cancelled (Queued):[/yellow] {job.id}")
                return

            # 2. Update status and notify
            job.status = JobStatus.RUNNING
            job.started_at = datetime.now(timezone.utc)
            await self.callbacks.emit_start(job)

            # 2b. Start the cost-budget watcher if the job has an effective
            #     cap. No-op when the budget modules are unavailable, the cap
            #     is None, or the cost CSV path is unset.
            self._start_watcher_for(job)

            # 3. Execute
            result = None

            if self._custom_executor:
                # Custom executors (the private GitHub App's pdd-issue
                # path) spawn their own subprocesses; they do NOT go
                # through _run_click_command. The integration
                # contract is that the custom executor calls
                # `JobManager.subprocess_env(job)` and passes the
                # result as `env=` to subprocess.Popen /
                # asyncio.create_subprocess_*; that is the only
                # concurrency-safe path for max_concurrent > 1.
                #
                # As a SAFETY NET for legacy executors that do not
                # know about subprocess_env yet, set
                # os.environ['PDD_JOB_ID'] when (and only when)
                # max_concurrent == 1 — sequential execution means no
                # other job can overwrite the env mid-flight. Restore
                # the prior value (or remove) in finally so the env
                # does not leak past this job's execution; under
                # max_concurrent=1 there is no concurrent reader to
                # race with. Under max_concurrent > 1 we leave
                # os.environ alone entirely.
                _env_safety_net = self.max_concurrent == 1
                _prior_job_id = (
                    os.environ.get('PDD_JOB_ID') if _env_safety_net else None
                )
                if _env_safety_net:
                    os.environ['PDD_JOB_ID'] = job.id
                try:
                    result = await self._custom_executor(job)
                finally:
                    if _env_safety_net:
                        if _prior_job_id is None:
                            os.environ.pop('PDD_JOB_ID', None)
                        else:
                            os.environ['PDD_JOB_ID'] = _prior_job_id
            else:
                result = await self._run_click_command(job)

            # 4. Handle Result
            if self._cancel_events[job.id].is_set():
                # Respect a terminal status already set by another path
                # (e.g. BUDGET_EXCEEDED from _handle_budget_exceeded).
                if job.status not in _TERMINAL_STATUSES:
                    job.status = JobStatus.CANCELLED
                console.print(f"[yellow]Job cancelled:[/yellow] {job.id}")
            else:
                job.result = result
                job.cost = float(result.get("cost", 0.0)) if isinstance(result, dict) else 0.0
                if job.status not in _TERMINAL_STATUSES:
                    job.status = JobStatus.COMPLETED
                console.print(f"[green]Job completed:[/green] {job.id}")

        except asyncio.CancelledError:
            # Do not demote a terminal status the budget watcher (or any
            # other handler) has already written. CancelledError is the
            # mechanism we use to stop subprocesses on a budget hit, so
            # BUDGET_EXCEEDED must survive this handler.
            if job.status not in _TERMINAL_STATUSES:
                job.status = JobStatus.CANCELLED
                console.print(f"[yellow]Job cancelled (Task):[/yellow] {job.id}")
            raise  # Re-raise to propagate cancellation

        except Exception as e:
            job.error = str(e)
            # Preserve captured output for debugging (live_stdout is updated by read_stream)
            if job.live_stdout or job.live_stderr:
                job.result = {
                    "stdout": job.live_stdout,
                    "stderr": job.live_stderr,
                    "exit_code": None,
                    "error_type": type(e).__name__,
                }
            if job.status not in _TERMINAL_STATUSES:
                job.status = JobStatus.FAILED
            console.print(f"[red]Job failed:[/red] {job.id} - {e}")
            
        finally:
            # 5. Cleanup and Notify
            if not job.completed_at:
                job.completed_at = datetime.now(timezone.utc)
            self._stop_watcher_for(job.id)
            await self.callbacks.emit_complete(job)

            if job.id in self._cancel_events:
                del self._cancel_events[job.id]

    async def _run_click_command(self, job: Job) -> Dict[str, Any]:
        """
        Run a PDD command as a subprocess with output streaming and cancellation support.

        This uses subprocess execution instead of direct Click invocation to enable:
        - Proper cancellation via SIGTERM/SIGKILL
        - Process isolation
        - Output streaming
        """
        # `pdd issue` is the GitHub App's autonomous-solving label-triggered
        # command — it does not exist as a public Click subcommand and is
        # only meaningful when JobManager has been constructed with a
        # custom `executor=` (the private App's executor). Fail loudly
        # here instead of spawning `pdd issue` and dying with
        # "No such command 'issue'" — that error misleads operators
        # into thinking the public CLI is broken when in fact the
        # job was misrouted.
        if job.command == "issue":
            raise RuntimeError(
                "command='issue' (pdd-issue autonomous solving) requires a "
                "custom JobManager executor (the private GitHub App). The "
                "public pdd CLI has no `issue` subcommand. Construct "
                "JobManager(executor=<your_executor>) or submit a public "
                "command (sync/generate/bug/change/fix/...)."
            )

        loop = asyncio.get_running_loop()

        # Build command args - add --force to skip confirmation prompts
        options_with_force = dict(job.options) if job.options else {}
        options_with_force['force'] = True  # Skip all confirmation prompts
        cmd_args = _build_subprocess_command_args(job.command, job.args, options_with_force)

        # Set up environment for headless execution. Per-job env keys
        # (PDD_JOB_ID, PDD_OUTPUT_COST_PATH) live in subprocess_env so
        # custom executors can share one helper without re-implementing
        # the isolation logic.
        env = self.subprocess_env(job)
        env['CI'] = '1'
        env['PDD_FORCE'] = '1'
        env['TERM'] = 'dumb'
        env['PDD_SKIP_UPDATE_CHECK'] = '1'  # Skip update prompts
        env['PDD_JOB_DEADLINE'] = str(time.time() + JOB_TIMEOUT)  # Budget for agentic retries

        stdout_lines = []
        stderr_lines = []

        def run_subprocess():
            """Run subprocess in thread with output streaming."""
            try:
                process = subprocess.Popen(
                    cmd_args,
                    stdout=subprocess.PIPE,
                    stderr=subprocess.PIPE,
                    stdin=subprocess.DEVNULL,
                    cwd=str(self.project_root),
                    env=env,
                    text=True,
                    bufsize=1,  # Line buffered
                )

                # Track process for cancellation
                with self._process_lock:
                    self._processes[job.id] = process

                # Read output in real-time
                def read_stream(stream, stream_type, lines_list):
                    try:
                        for line in iter(stream.readline, ''):
                            if line:
                                lines_list.append(line)
                                # Update live output on the job for polling
                                if stream_type == "stdout":
                                    job.live_stdout += line
                                else:
                                    job.live_stderr += line
                                # Emit output callback
                                if job.status == JobStatus.RUNNING:
                                    asyncio.run_coroutine_threadsafe(
                                        self.callbacks.emit_output(job, stream_type, line),
                                        loop
                                    )
                    except Exception:
                        pass
                    finally:
                        stream.close()

                # Start threads to read stdout and stderr
                stdout_thread = threading.Thread(
                    target=read_stream,
                    args=(process.stdout, "stdout", stdout_lines)
                )
                stderr_thread = threading.Thread(
                    target=read_stream,
                    args=(process.stderr, "stderr", stderr_lines)
                )

                stdout_thread.start()
                stderr_thread.start()

                # Wait for process to complete with timeout
                start_wall = time.time()
                while True:
                    elapsed = time.time() - start_wall
                    remaining = max(JOB_TIMEOUT - elapsed, 0)
                    try:
                        exit_code = process.wait(timeout=min(60, remaining))
                        break
                    except subprocess.TimeoutExpired:
                        if time.time() - start_wall >= JOB_TIMEOUT:
                            process.terminate()
                            try:
                                process.wait(timeout=10)
                            except subprocess.TimeoutExpired:
                                process.kill()
                                try:
                                    process.wait(timeout=10)
                                except subprocess.TimeoutExpired:
                                    logger.warning(
                                        "Process %d did not exit after SIGKILL; possible zombie process",
                                        process.pid,
                                    )
                            raise RuntimeError(
                                f"Job timed out after {JOB_TIMEOUT}s and was killed"
                            )

                # Wait for output threads to finish
                stdout_thread.join(timeout=5)
                stderr_thread.join(timeout=5)

                return exit_code

            finally:
                # Clean up process tracking
                with self._process_lock:
                    self._processes.pop(job.id, None)

        # Run in thread pool
        exit_code = await loop.run_in_executor(self._thread_pool, run_subprocess)

        # Check if cancelled
        if self._cancel_events.get(job.id) and self._cancel_events[job.id].is_set():
            raise asyncio.CancelledError("Job was cancelled")

        stdout_text = ''.join(stdout_lines)
        stderr_text = ''.join(stderr_lines)

        # For sync command, check stdout for failure indicators even if exit_code is 0
        # This handles the case where sync returns 0 but actually failed
        if exit_code == 0 and job.command == "sync":
            # Look for the summary line printed by sync_main.py
            # It prints: "Overall status: [red]Failed[/red]" or "Overall status: [green]Success[/green]"
            # Check "Failed" only on the "Overall status:" line itself, not anywhere in stdout,
            # since other code (e.g. get_jwt_token.py keyring warnings) may print "Failed" elsewhere.
            for line in stdout_text.splitlines():
                if "Overall status:" in line and "Failed" in line:
                    # Surface architecture-conformance details (issue #865) when
                    # present, instead of a generic "Sync operation failed".
                    conformance_msg = _extract_architecture_conformance_error(
                        stdout_text, stderr_text, job.command, job.args
                    )
                    if conformance_msg:
                        raise RuntimeError(conformance_msg)
                    raise RuntimeError("Sync operation failed (see output for details)")

        if exit_code is not None and exit_code < 0:
            sig_num = -exit_code
            raise RuntimeError(
                f"Process killed by signal {sig_num} (possible OOM or external termination)"
            )

        if exit_code != 0:
            # Surface architecture-conformance details (issue #865) when sync
            # subprocess fails with conformance markers in its output.
            if job.command == "sync":
                conformance_msg = _extract_architecture_conformance_error(
                    stdout_text, stderr_text, job.command, job.args
                )
                if conformance_msg:
                    raise RuntimeError(conformance_msg)

            # Combine stdout and stderr for complete error context
            # Filter out INFO/DEBUG logs to find the actual error message
            all_output = stdout_text + "\n" + stderr_text if stderr_text else stdout_text

            # Try to find actual error lines (not INFO/DEBUG logs)
            error_lines = []
            for line in all_output.split('\n'):
                line_stripped = line.strip()
                if not line_stripped:
                    continue
                # Skip common log prefixes
                if ' - INFO - ' in line or ' - DEBUG - ' in line:
                    continue
                # Skip lines that are just timestamps with INFO
                if line_stripped.startswith('202') and ' INFO ' in line:
                    continue
                error_lines.append(line)

            if error_lines:
                error_msg = '\n'.join(error_lines[-50:])  # Last 50 non-INFO lines
            else:
                # No non-INFO lines found, use all output
                error_msg = all_output or f"Command failed with exit code {exit_code}"

            raise RuntimeError(error_msg)

        return {
            "stdout": stdout_text,
            "stderr": stderr_text,
            "exit_code": exit_code,
            "cost": 0.0
        }

    def get_job(self, job_id: str) -> Optional[Job]:
        return self._jobs.get(job_id)

    def get_all_jobs(self) -> Dict[str, Job]:
        return self._jobs.copy()

    def get_active_jobs(self) -> Dict[str, Job]:
        return {
            job_id: job
            for job_id, job in self._jobs.items()
            if job.status in (JobStatus.QUEUED, JobStatus.RUNNING)
        }

    def get_budget(self, job_id: str) -> BudgetSettings:
        """Return a :class:`BudgetSettings` snapshot for ``job_id``.

        Raises ``KeyError`` (with ``job_id`` as ``args[0]``) when the job is
        not known to the manager. The ``commands`` route maps this to
        HTTP 404.
        """
        job = self._jobs.get(job_id)
        if job is None:
            raise KeyError(job_id)
        if _effective_cap_fn is None:
            raise RuntimeError("budget_settings module unavailable")
        cap = _effective_cap_fn(
            job.command,
            budget_cap=job.budget_cap,
            node_budget=job.node_budget,
            max_total_cap=job.max_total_cap,
            node_count=job.node_count,
        )
        spent = job.cost
        if self._budget_store is not None:
            existing = self._budget_store.get(job_id)
            if existing is not None and existing.spent_so_far > spent:
                spent = existing.spent_so_far
        # Fall back to the live watcher spent if available; the watcher's
        # last poll may be slightly fresher than `job.cost`, which is only
        # set on subprocess exit.
        watcher = self._watchers.get(job_id)
        if watcher is not None:
            try:
                live = watcher.spent()
                if live > spent:
                    spent = live
            except Exception:  # noqa: BLE001
                pass
        return BudgetSettings(
            command=job.command,
            node_budget=job.node_budget,
            max_total_cap=job.max_total_cap,
            budget_cap=job.budget_cap,
            effective_cap=cap,
            spent_so_far=spent,
            status=job.status,
            node_count=job.node_count,
        )

    async def update_budget(
        self,
        job_id: str,
        *,
        budget_cap: Any = _UNSET,
        node_budget: Any = _UNSET,
        max_total_cap: Any = _UNSET,
        node_count: Any = _UNSET,
    ) -> Job:
        """Apply a mid-run budget change to ``job_id``.

        Exceptions are part of the public contract — the ``commands`` route
        maps them to HTTP statuses by type, never by message text:
          * ``KeyError`` (``args[0] == job_id``) → 404, unknown job;
          * ``RuntimeError`` with message starting ``"job not active: "`` →
            409, job is in a terminal status;
          * ``ValueError`` → 400, an amount failed
            :func:`budget_settings.validate_amount`.
        """
        job = self._jobs.get(job_id)
        if job is None:
            raise KeyError(job_id)
        if job.status in (
            JobStatus.COMPLETED,
            JobStatus.FAILED,
            JobStatus.CANCELLED,
            JobStatus.BUDGET_EXCEEDED,
        ):
            raise RuntimeError(f"job not active: {job_id}")

        if validate_amount is None or _effective_cap_fn is None:
            raise RuntimeError("budget_settings module unavailable")

        if budget_cap is not _UNSET and budget_cap is not None:
            job.budget_cap = validate_amount(budget_cap)
        elif budget_cap is None and budget_cap is not _UNSET:
            job.budget_cap = None
        if node_budget is not _UNSET and node_budget is not None:
            job.node_budget = validate_amount(node_budget)
        elif node_budget is None and node_budget is not _UNSET:
            job.node_budget = None
        if max_total_cap is not _UNSET and max_total_cap is not None:
            job.max_total_cap = validate_amount(max_total_cap)
        elif max_total_cap is None and max_total_cap is not _UNSET:
            job.max_total_cap = None
        if node_count is not _UNSET:
            if node_count is None:
                job.node_count = None
            else:
                job.node_count = _coerce_node_count_strict(node_count)

        new_cap = _effective_cap_fn(
            job.command,
            budget_cap=job.budget_cap,
            node_budget=job.node_budget,
            max_total_cap=job.max_total_cap,
            node_count=job.node_count,
        )
        watcher = self._watchers.get(job_id)
        if watcher is not None:
            try:
                watcher.update_cap(new_cap)
            except Exception as exc:  # noqa: BLE001
                console.print(f"[red]update_cap failed for {job_id}: {exc}[/red]")
        elif new_cap is not None:
            # No watcher running yet (e.g. cap was None at submit and is
            # being set for the first time). Start one if the job is still
            # active.
            self._start_watcher_for(job)

        if self._budget_store is not None:
            try:
                self._budget_store.update(
                    job_id,
                    budget_cap=job.budget_cap,
                    node_budget=job.node_budget,
                    max_total_cap=job.max_total_cap,
                    node_count=job.node_count,
                    status=job.status,
                )
            except KeyError:
                # Store snapshot not yet created (watcher never started).
                pass
        return job

    def update_node_count(self, job_id: str, node_count: int) -> Job:
        """Synchronous helper for the executor to push solving-tree
        progress without paying for an awaitable round-trip.

        Equivalent to ``update_budget(node_count=node_count)`` but skips
        the budget-only kwargs and runs synchronously, since this is
        called from the subprocess driver thread.
        """
        job = self._jobs.get(job_id)
        if job is None:
            raise KeyError(job_id)
        node_count = _coerce_node_count_strict(node_count)
        job.node_count = node_count
        if _effective_cap_fn is not None:
            new_cap = _effective_cap_fn(
                job.command,
                budget_cap=job.budget_cap,
                node_budget=job.node_budget,
                max_total_cap=job.max_total_cap,
                node_count=node_count,
            )
            watcher = self._watchers.get(job_id)
            if watcher is not None:
                try:
                    watcher.update_cap(new_cap)
                except Exception as exc:  # noqa: BLE001
                    console.print(
                        f"[red]update_cap failed for {job_id}: {exc}[/red]"
                    )
            if self._budget_store is not None:
                try:
                    self._budget_store.update(
                        job_id, node_count=node_count, status=job.status
                    )
                except KeyError:
                    pass
        return job

    async def cancel(self, job_id: str) -> bool:
        """
        Cancel a running job by terminating its subprocess.

        This method:
        1. Sets the cancel event to signal cancellation
        2. Terminates the subprocess (SIGTERM, then SIGKILL if needed)
        3. Cancels the async task

        Returns True if cancellation was initiated, False if job already finished.
        """
        job = self._jobs.get(job_id)
        if not job:
            return False

        if job.status in (JobStatus.COMPLETED, JobStatus.FAILED, JobStatus.CANCELLED):
            return False

        # Set cancel event first
        if job_id in self._cancel_events:
            self._cancel_events[job_id].set()

        # Terminate the subprocess if running
        with self._process_lock:
            process = self._processes.get(job_id)
            if process and process.poll() is None:
                console.print(f"[yellow]Terminating subprocess for job:[/yellow] {job_id}")
                try:
                    # Try graceful termination first
                    process.terminate()

                    # Give it a moment to terminate
                    try:
                        process.wait(timeout=2)
                    except subprocess.TimeoutExpired:
                        # Force kill if it doesn't respond
                        console.print(f"[yellow]Force killing subprocess for job:[/yellow] {job_id}")
                        process.kill()
                        process.wait(timeout=2)
                except Exception as e:
                    console.print(f"[red]Error terminating subprocess: {e}[/red]")

        # Cancel the async task
        if job_id in self._tasks:
            self._tasks[job_id].cancel()

        # Update job status — but never demote a terminal status set by
        # another handler (e.g. BUDGET_EXCEEDED already set by
        # _handle_budget_exceeded before it called cancel()).
        if job.status not in _TERMINAL_STATUSES:
            job.status = JobStatus.CANCELLED
        job.completed_at = datetime.now(timezone.utc)

        console.print(f"[yellow]Cancellation completed for job:[/yellow] {job_id}")
        return True

    def cleanup_old_jobs(self, max_age_seconds: float = 3600) -> int:
        now = datetime.now(timezone.utc)
        to_remove = []

        for job_id, job in self._jobs.items():
            if job.completed_at:
                age = (now - job.completed_at).total_seconds()
                if age > max_age_seconds:
                    to_remove.append(job_id)

        for job_id in to_remove:
            del self._jobs[job_id]
            if job_id in self._cancel_events:
                del self._cancel_events[job_id]
            if job_id in self._tasks:
                del self._tasks[job_id]

        if to_remove:
            console.print(f"[dim]Cleaned up {len(to_remove)} old jobs[/dim]")
            
        return len(to_remove)

    async def shutdown(self) -> None:
        console.print("[bold red]Shutting down JobManager...[/bold red]")
        
        active_jobs = list(self.get_active_jobs().keys())
        for job_id in active_jobs:
            await self.cancel(job_id)

        if active_jobs:
            await asyncio.sleep(0.1)

        self._thread_pool.shutdown(wait=False)