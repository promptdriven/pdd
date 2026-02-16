"""
Async sync runner: parallel module sync with dependency-aware scheduling.

Manages concurrent `pdd sync` subprocesses, respects dependency ordering,
updates a live GitHub issue comment with progress, and pauses on failure.
"""
from __future__ import annotations

import csv
import datetime
import json
import os
import re
import signal
import subprocess
import sys
import tempfile
import threading
import time
from concurrent.futures import FIRST_COMPLETED, ThreadPoolExecutor, wait
from dataclasses import dataclass, field
from pathlib import Path
from typing import Any, Dict, List, Optional, Tuple

from rich.console import Console

from .sync_order import extract_module_from_include

console = Console()

# Regex matching lines composed entirely of box-drawing / table characters
# (Rich Panel borders, table separators, etc.) — used to skip them in heartbeat.
_BOX_CHARS_RE = re.compile(r'^[\s╭╮╰╯─│┌┐└┘├┤┬┴┼═║╔╗╚╝╠╣╦╩╬\-|+]*$')

# Maximum concurrent syncs
MAX_WORKERS = 4
# Per-module timeout in seconds (30 min — complex modules need generate+crash+verify+test)
MODULE_TIMEOUT = 1800
# State file for resumability (relative to project root)
STATE_FILE_PATH = ".pdd/agentic_sync_state.json"


@dataclass
class ModuleState:
    """Tracks the execution state of a single module sync."""

    status: str = "pending"  # pending, running, success, failed
    start_time: Optional[float] = None
    end_time: Optional[float] = None
    cost: float = 0.0
    error: Optional[str] = None
    current_phase: Optional[str] = None
    completed_phases: List[str] = field(default_factory=list)


def _find_pdd_executable() -> Optional[str]:
    """Find the pdd executable path."""
    import shutil

    pdd_path = shutil.which("pdd")
    if pdd_path:
        return pdd_path

    python_dir = Path(sys.executable).parent
    pdd_in_python_dir = python_dir / "pdd"
    if pdd_in_python_dir.exists():
        return str(pdd_in_python_dir)

    return None


def _parse_cost_from_csv(csv_path: str) -> float:
    """Parse total cost from a PDD_OUTPUT_COST_PATH CSV file."""
    total = 0.0
    try:
        with open(csv_path, "r", encoding="utf-8") as f:
            reader = csv.DictReader(f)
            for row in reader:
                cost_val = row.get("cost", "")
                if cost_val:
                    try:
                        total += float(cost_val)
                    except (ValueError, TypeError):
                        pass
    except (OSError, csv.Error):
        pass
    return total


def build_dep_graph_from_architecture(
    arch_path: Path, target_basenames: List[str]
) -> Dict[str, List[str]]:
    """
    Build dependency subgraph for target basenames from architecture.json.

    Args:
        arch_path: Path to architecture.json.
        target_basenames: List of module basenames to include.

    Returns:
        Dict mapping basename -> [dependency basenames] (only within target set).
    """
    try:
        with open(arch_path, "r", encoding="utf-8") as f:
            arch = json.load(f)
    except (OSError, json.JSONDecodeError):
        return {b: [] for b in target_basenames}

    if not isinstance(arch, list):
        return {b: [] for b in target_basenames}

    # Map prompt filename -> stripped basename (e.g., "crm_models_Python.prompt" -> "crm_models")
    filename_to_basename: Dict[str, str] = {}
    for entry in arch:
        filename = entry.get("filename", "")
        basename = extract_module_from_include(filename)
        if basename:
            filename_to_basename[filename] = basename

    # Target basenames may include a language suffix (e.g., "crm_models_Python")
    # that extract_module_from_include strips. Build a lookup from stripped name
    # to the original target basename so we can match architecture entries.
    stripped_to_target: Dict[str, str] = {}
    for tb in target_basenames:
        stripped_to_target[tb] = tb  # exact match first
        stripped = extract_module_from_include(tb + ".prompt")
        if stripped:
            stripped_to_target[stripped] = tb

    target_set = set(stripped_to_target.keys())

    # Build graph using original target basenames
    graph: Dict[str, List[str]] = {}
    for entry in arch:
        basename = filename_to_basename.get(entry.get("filename", ""))
        if basename and basename in target_set:
            target_name = stripped_to_target[basename]
            deps = []
            for dep_filename in entry.get("dependencies", []):
                dep_basename = filename_to_basename.get(dep_filename)
                if dep_basename and dep_basename in target_set and dep_basename != basename:
                    deps.append(stripped_to_target[dep_basename])
            graph[target_name] = deps

    # Ensure all target basenames are in graph
    for b in target_basenames:
        if b not in graph:
            graph[b] = []

    return graph


class AsyncSyncRunner:
    """
    Parallel sync engine that runs `pdd sync` for multiple modules concurrently,
    respecting dependency order and posting live progress to GitHub.
    """

    def __init__(
        self,
        basenames: List[str],
        dep_graph: Dict[str, List[str]],
        sync_options: Dict[str, Any],
        github_info: Optional[Dict[str, Any]],
        quiet: bool = False,
        verbose: bool = False,
        issue_url: Optional[str] = None,
    ):
        self.basenames = basenames
        self.dep_graph = dep_graph
        self.sync_options = sync_options
        self.github_info = github_info
        self.quiet = quiet
        self.verbose = verbose
        self.issue_url = issue_url
        self.project_root = Path.cwd()

        self.module_states: Dict[str, ModuleState] = {
            b: ModuleState() for b in basenames
        }
        self.failed = False
        self.comment_id: Optional[int] = None
        self.lock = threading.Lock()

        # Track child process groups for cleanup on interrupt
        self._child_pgids: set = set()

        # Rate-limit GitHub comment updates for phase changes
        self._last_comment_update: float = 0.0
        self._comment_update_interval: float = 15.0  # seconds

        # Try to resume from saved state
        self._resumed_modules: List[str] = []
        self._load_state()

    def _state_file_path(self) -> Path:
        """Return the path to the state file."""
        return self.project_root / STATE_FILE_PATH

    def _load_state(self) -> None:
        """Load previously saved state if it matches the current run."""
        if not self.issue_url:
            return

        state_path = self._state_file_path()
        if not state_path.exists():
            return

        try:
            with open(state_path, "r", encoding="utf-8") as f:
                saved = json.load(f)
        except (OSError, json.JSONDecodeError):
            return

        # Must match the same issue URL and module list
        if saved.get("issue_url") != self.issue_url:
            return
        saved_modules = saved.get("modules", {})
        if set(saved_modules.keys()) != set(self.basenames):
            return

        # Restore succeeded modules and comment_id
        for basename, info in saved_modules.items():
            if info.get("status") == "success":
                self.module_states[basename].status = "success"
                self.module_states[basename].cost = info.get("cost", 0.0)
                self._resumed_modules.append(basename)

        self.comment_id = saved.get("comment_id")

    def _save_state(self) -> None:
        """Atomically persist current state to disk."""
        if not self.issue_url:
            return

        state_path = self._state_file_path()
        state_path.parent.mkdir(parents=True, exist_ok=True)

        modules_data = {}
        with self.lock:
            for basename in self.basenames:
                state = self.module_states[basename]
                modules_data[basename] = {
                    "status": state.status,
                    "cost": state.cost,
                }

        data = {
            "issue_url": self.issue_url,
            "modules": modules_data,
            "total_cost": sum(m["cost"] for m in modules_data.values()),
            "comment_id": self.comment_id,
            "started_at": datetime.datetime.now(datetime.timezone.utc).isoformat(),
        }

        # Atomic write via temp file + os.replace
        try:
            fd, tmp_path = tempfile.mkstemp(
                dir=str(state_path.parent), suffix=".tmp"
            )
            with os.fdopen(fd, "w", encoding="utf-8") as f:
                json.dump(data, f, indent=2)
            os.replace(tmp_path, str(state_path))
        except OSError:
            # Best-effort; don't break sync for state persistence failures
            try:
                os.unlink(tmp_path)
            except OSError:
                pass

    def _delete_state(self) -> None:
        """Remove the state file (called on full success)."""
        try:
            self._state_file_path().unlink(missing_ok=True)
        except OSError:
            pass

    def _kill_children(self) -> None:
        """Kill all tracked child process groups."""
        for pgid in list(self._child_pgids):
            try:
                os.killpg(pgid, signal.SIGTERM)
            except OSError:
                pass
        # Give children a moment to exit, then force-kill survivors
        time.sleep(1)
        for pgid in list(self._child_pgids):
            try:
                os.killpg(pgid, signal.SIGKILL)
            except OSError:
                pass
        self._child_pgids.clear()

    def run(self) -> Tuple[bool, str, float]:
        """
        Run all syncs respecting dependencies.

        Returns:
            Tuple of (all_success, summary_message, total_cost).
        """
        if not self.basenames:
            return True, "No modules to sync", 0.0

        if self._resumed_modules and not self.quiet:
            console.print(
                f"[green]Resuming: skipping {len(self._resumed_modules)} already-succeeded "
                f"module(s): {self._resumed_modules}[/green]"
            )
            fresh = [b for b in self.basenames if b not in self._resumed_modules]
            if fresh:
                console.print(f"[blue]Modules to sync: {fresh}[/blue]")

        self._update_github_comment()

        # Install signal handler so Ctrl+C kills child processes instead of orphaning them
        prev_sigint = signal.getsignal(signal.SIGINT)
        prev_sigterm = signal.getsignal(signal.SIGTERM)

        def _on_interrupt(signum, frame):
            """Kill children then re-raise."""
            self._kill_children()
            # Restore and re-raise so the parent sees the interrupt
            signal.signal(signum, prev_sigint if signum == signal.SIGINT else prev_sigterm)
            os.kill(os.getpid(), signum)

        signal.signal(signal.SIGINT, _on_interrupt)
        signal.signal(signal.SIGTERM, _on_interrupt)

        try:
            return self._run_inner()
        finally:
            # Restore original handlers and clean up any remaining children
            signal.signal(signal.SIGINT, prev_sigint)
            signal.signal(signal.SIGTERM, prev_sigterm)
            self._kill_children()

    def _run_inner(self) -> Tuple[bool, str, float]:
        """Inner run loop, separated so signal handlers can be set up around it."""
        with ThreadPoolExecutor(max_workers=MAX_WORKERS) as executor:
            futures: Dict[Any, str] = {}  # Future -> basename

            while not self._all_done():
                # Find modules whose deps are all "success"
                ready = self._get_ready_modules()

                if self.failed:
                    # Don't start new modules; wait for running ones to finish
                    if not futures:
                        break
                else:
                    # Only submit up to available worker slots so modules
                    # aren't marked "running" while queued in the executor.
                    available_slots = MAX_WORKERS - len(futures)
                    for basename in ready[:available_slots]:
                        with self.lock:
                            self.module_states[basename].status = "running"
                            self.module_states[basename].start_time = time.time()
                        self._update_github_comment()
                        future = executor.submit(self._sync_one_module, basename)
                        futures[future] = basename

                if not futures:
                    # No futures running and nothing ready — check for blocked modules
                    blocked = self._get_blocked_modules()
                    if blocked and not self.failed:
                        # Modules are blocked by failed deps
                        self.failed = True
                    break

                # Wait for at least one future to complete
                done, _ = wait(futures, return_when=FIRST_COMPLETED)
                for future in done:
                    basename = futures.pop(future)
                    try:
                        success, cost, error = future.result()
                    except Exception as e:
                        success, cost, error = False, 0.0, str(e)
                    self._record_result(basename, success, cost, error)
                    self._update_github_comment()
                    if not success:
                        self.failed = True

        # Final update
        self._update_github_comment()

        # Build summary
        total_cost = sum(s.cost for s in self.module_states.values())
        succeeded = [b for b, s in self.module_states.items() if s.status == "success"]
        failed = [b for b, s in self.module_states.items() if s.status == "failed"]
        pending = [b for b, s in self.module_states.items() if s.status == "pending"]

        if failed:
            msg = f"Failed: {failed}. Succeeded: {succeeded}."
            if pending:
                msg += f" Skipped (blocked): {pending}."
            # Include error details for failed modules
            for b in failed:
                err = self.module_states[b].error
                if err:
                    # Truncate long errors but keep enough context
                    err_summary = err.strip()[:500]
                    msg += f"\n  {b}: {err_summary}"
            self._save_state()
            return False, msg, total_cost
        elif pending:
            msg = f"Succeeded: {succeeded}. Skipped (blocked): {pending}."
            self._save_state()
            return False, msg, total_cost
        else:
            self._delete_state()
            return True, f"All {len(succeeded)} modules synced successfully", total_cost

    def _all_done(self) -> bool:
        """Check if all modules are in a terminal state."""
        with self.lock:
            return all(
                s.status in ("success", "failed")
                for s in self.module_states.values()
            )

    def _get_ready_modules(self) -> List[str]:
        """Get modules whose deps are all satisfied and that are pending."""
        ready = []
        with self.lock:
            for basename in self.basenames:
                state = self.module_states[basename]
                if state.status != "pending":
                    continue
                deps = self.dep_graph.get(basename, [])
                # All deps must be "success" (deps not in basenames are assumed ok)
                deps_satisfied = all(
                    self.module_states.get(d, ModuleState(status="success")).status == "success"
                    for d in deps
                )
                if deps_satisfied:
                    ready.append(basename)
        return ready

    def _get_blocked_modules(self) -> List[str]:
        """Get modules that are pending but blocked by non-success deps."""
        blocked = []
        with self.lock:
            for basename in self.basenames:
                state = self.module_states[basename]
                if state.status != "pending":
                    continue
                deps = self.dep_graph.get(basename, [])
                has_failed_dep = any(
                    self.module_states.get(d, ModuleState(status="success")).status == "failed"
                    for d in deps
                )
                if has_failed_dep:
                    blocked.append(basename)
        return blocked

    def _record_result(self, basename: str, success: bool, cost: float, error: str) -> None:
        """Record the result of a module sync and persist state."""
        with self.lock:
            state = self.module_states[basename]
            state.status = "success" if success else "failed"
            state.end_time = time.time()
            state.cost = cost
            if not success:
                state.error = error
            # Finalize phase tracking: move current_phase to completed
            if state.current_phase and not state.current_phase.startswith("skip:"):
                state.completed_phases.append(state.current_phase)
            state.current_phase = None
        self._save_state()

    def _on_phase_change(self, basename: str, phase: str) -> None:
        """Handle a phase transition for a module."""
        with self.lock:
            state = self.module_states[basename]
            if state.current_phase and state.current_phase != phase:
                # Previous phase completed
                if not state.current_phase.startswith("skip:"):
                    state.completed_phases.append(state.current_phase)
            state.current_phase = phase
        # Rate-limited comment update
        self._update_github_comment_throttled()

    def _update_github_comment_throttled(self) -> None:
        """Update comment at most once per interval."""
        now = time.time()
        if now - self._last_comment_update >= self._comment_update_interval:
            self._last_comment_update = now
            self._update_github_comment()

    def _sync_one_module(self, basename: str) -> Tuple[bool, float, str]:
        """
        Run pdd sync for a single module as a subprocess.

        Uses Popen with threaded pipe readers to prevent deadlock when
        subprocess output exceeds the OS pipe buffer (~64KB).

        Returns:
            Tuple of (success, cost, error_message).
        """
        pdd_exe = _find_pdd_executable()
        if pdd_exe:
            cmd = [pdd_exe]
        else:
            cmd = [sys.executable, "-m", "pdd"]

        # Global options first
        cmd.append("--force")

        # Command + positional arg
        cmd.extend(["sync", basename])

        # Command-specific options
        # Always pass --agentic and --no-steer: child subprocess is headless (stdin=/dev/null)
        cmd.append("--agentic")
        cmd.append("--no-steer")
        if self.sync_options.get("skip_verify"):
            cmd.append("--skip-verify")
        if self.sync_options.get("skip_tests"):
            cmd.append("--skip-tests")
        if self.sync_options.get("budget"):
            cmd.extend(["--budget", str(self.sync_options["budget"])])
        if self.sync_options.get("max_attempts"):
            cmd.extend(["--max-attempts", str(self.sync_options["max_attempts"])])

        # Set up environment for headless mode and cost capture
        cost_file = tempfile.NamedTemporaryFile(suffix=".csv", delete=False)
        cost_file.close()

        env = os.environ.copy()
        env["PDD_OUTPUT_COST_PATH"] = cost_file.name
        env["CI"] = "1"
        env["PDD_FORCE"] = "1"
        env["PDD_AUTO_UPDATE"] = "false"
        env["TERM"] = "dumb"
        env["PYTHONUNBUFFERED"] = "1"

        if not self.quiet:
            console.print(f"[blue]Starting sync: {basename}[/blue]")

        stdout_lines: List[str] = []
        stderr_lines: List[str] = []
        verbose_print = self.verbose and not self.quiet

        def _read_stream(stream, lines_list: List[str], prefix: str = "") -> None:
            """Drain a pipe stream line-by-line into a list."""
            try:
                for line in iter(stream.readline, ''):
                    if line:
                        lines_list.append(line)
                        # Parse phase markers emitted by sync_orchestration
                        stripped = line.strip()
                        if stripped.startswith("PDD_PHASE: "):
                            phase = stripped[len("PDD_PHASE: "):]
                            self._on_phase_change(basename, phase)
                        if verbose_print:
                            console.print(f"[dim]{prefix}{basename}>[/dim] {line.rstrip()}")
            except Exception:
                pass
            finally:
                stream.close()

        try:
            process = subprocess.Popen(
                cmd,
                stdout=subprocess.PIPE,
                stderr=subprocess.PIPE,
                stdin=subprocess.DEVNULL,
                cwd=str(self.project_root),
                env=env,
                text=True,
                bufsize=1,  # Line buffered
                start_new_session=True,  # Create process group for clean kill
            )
            # Track the process group so we can kill it on Ctrl+C
            self._child_pgids.add(process.pid)
        except Exception as e:
            return False, _parse_cost_from_csv(cost_file.name), str(e)

        t_out = threading.Thread(
            target=_read_stream, args=(process.stdout, stdout_lines, ""), daemon=True
        )
        t_err = threading.Thread(
            target=_read_stream, args=(process.stderr, stderr_lines, "err:"), daemon=True
        )
        t_out.start()
        t_err.start()

        try:
            # Poll with heartbeat so user sees progress in non-verbose mode
            heartbeat_interval = 60  # seconds
            start_wall = self.module_states[basename].start_time or time.time()
            last_heartbeat = time.time()
            while True:
                elapsed_total = time.time() - start_wall
                remaining = max(MODULE_TIMEOUT - elapsed_total, 0)
                try:
                    exit_code = process.wait(timeout=min(heartbeat_interval, remaining))
                    break  # Process finished
                except subprocess.TimeoutExpired:
                    elapsed_total = time.time() - start_wall
                    if elapsed_total >= MODULE_TIMEOUT:
                        raise  # Re-raise to hit the timeout handler below
                    now = time.time()
                    if not self.quiet and now - last_heartbeat >= heartbeat_interval:
                        mins = int(elapsed_total) // 60
                        secs = int(elapsed_total) % 60
                        last_line = ""
                        for line in reversed(stdout_lines):
                            stripped = line.strip()
                            if stripped and not _BOX_CHARS_RE.match(stripped):
                                last_line = stripped
                                break
                        hint = f" — {last_line[:80]}" if last_line else ""
                        console.print(
                            f"[dim]  {basename}: still running ({mins}m{secs}s){hint}[/dim]"
                        )
                        last_heartbeat = now
        except subprocess.TimeoutExpired:
            # Kill entire process group (includes grandchild agentic subprocesses)
            try:
                os.killpg(process.pid, signal.SIGTERM)
            except OSError:
                process.terminate()
            try:
                process.wait(timeout=10)
            except subprocess.TimeoutExpired:
                try:
                    os.killpg(process.pid, signal.SIGKILL)
                except OSError:
                    process.kill()
                process.wait()
            self._child_pgids.discard(process.pid)
            return False, _parse_cost_from_csv(cost_file.name), f"Timeout after {MODULE_TIMEOUT}s"
        finally:
            self._child_pgids.discard(process.pid)
            t_out.join(timeout=5)
            t_err.join(timeout=5)

        cost = _parse_cost_from_csv(cost_file.name)

        # Clean up cost file
        try:
            os.unlink(cost_file.name)
        except OSError:
            pass

        stdout = "".join(stdout_lines)
        stderr = "".join(stderr_lines)

        # Detect success
        success = exit_code == 0
        if success:
            for line in stdout.splitlines():
                if "Overall status:" in line and "Failed" in line:
                    success = False
                    break

        if not self.quiet:
            status_str = "success" if success else "FAILED"
            console.print(f"[{'green' if success else 'red'}]Sync {basename}: {status_str}[/{'green' if success else 'red'}]")

        error = ""
        if not success:
            # Extract meaningful error lines from stderr and stdout,
            # filtering out INFO/DEBUG log noise
            all_output = (stderr or "") + "\n" + (stdout or "")
            error_lines = [
                line for line in all_output.splitlines()
                if line.strip() and not re.match(
                    r"^\d{4}-\d{2}-\d{2} .* - (INFO|DEBUG)( |-)", line
                )
            ]
            # Prefer lines containing error/traceback keywords
            keyword_lines = [
                line for line in error_lines
                if any(kw in line.lower() for kw in ("error", "failed", "traceback", "exception", "abort"))
            ]
            if keyword_lines:
                error = "\n".join(keyword_lines[-20:])
            elif error_lines:
                error = "\n".join(error_lines[-20:])
            else:
                error = f"Exit code {exit_code}"
            if not self.quiet:
                console.print(f"[red]  Error for {basename}:[/red] {error[:500]}")

        return success, cost, error

    def _update_github_comment(self) -> None:
        """Create or update a GitHub issue comment with current progress."""
        if not self.github_info:
            return

        owner = self.github_info["owner"]
        repo = self.github_info["repo"]
        issue_number = self.github_info["issue_number"]

        body = self._build_comment_body(issue_number)

        # Use a timeout to prevent gh API calls from blocking the runner
        gh_timeout = 30

        try:
            if self.comment_id is None:
                # Create new comment
                from .agentic_change import _run_gh_command

                ok, response = _run_gh_command([
                    "api", f"repos/{owner}/{repo}/issues/{issue_number}/comments",
                    "-X", "POST", "-f", f"body={body}",
                ], timeout=gh_timeout)
                if ok:
                    try:
                        data = json.loads(response)
                        self.comment_id = data.get("id")
                    except json.JSONDecodeError:
                        pass
            else:
                # Update existing comment
                from .agentic_change import _run_gh_command

                _run_gh_command([
                    "api", f"repos/{owner}/{repo}/issues/comments/{self.comment_id}",
                    "-X", "PATCH", "-f", f"body={body}",
                ], timeout=gh_timeout)
        except Exception:
            pass  # Don't break sync for comment failures

    def _build_comment_body(self, issue_number: int) -> str:
        """Build the markdown comment body showing sync progress."""
        lines = [
            "## PDD Agentic Sync Progress",
            f"Issue: #{issue_number}",
            "",
            "| Module | Status | Phase | Duration | Cost |",
            "|--------|--------|-------|----------|------|",
        ]

        total_cost = 0.0
        completed = 0
        total = len(self.basenames)

        with self.lock:
            for basename in self.basenames:
                state = self.module_states[basename]
                total_cost += state.cost

                if state.status == "success":
                    icon = "✅ Success"
                    completed += 1
                    duration = _format_duration(state.start_time, state.end_time)
                    cost_str = f"${state.cost:.2f}"
                    total_phases = len(state.completed_phases)
                    phase_str = f"{total_phases} phases" if total_phases else "-"
                elif state.status == "failed":
                    icon = "❌ Failed"
                    completed += 1
                    duration = _format_duration(state.start_time, state.end_time)
                    cost_str = f"${state.cost:.2f}"
                    total_phases = len(state.completed_phases)
                    phase_str = f"{total_phases} phases" if total_phases else "-"
                elif state.status == "running":
                    icon = "🔄 Running"
                    duration = _format_duration(state.start_time, time.time())
                    cost_str = "-"
                    if state.current_phase:
                        phase_name = state.current_phase.replace("skip:", "~")
                        done_count = len(state.completed_phases)
                        phase_str = f"`{phase_name}` ({done_count} done)" if done_count else f"`{phase_name}`"
                    else:
                        phase_str = "-"
                else:
                    icon = "⏳ Pending"
                    duration = "-"
                    cost_str = "-"
                    phase_str = "-"

                lines.append(f"| {basename} | {icon} | {phase_str} | {duration} | {cost_str} |")

        lines.append("")
        lines.append(f"**Total cost:** ${total_cost:.2f}")

        # Status line
        failed_modules = [b for b, s in self.module_states.items() if s.status == "failed"]
        all_done = all(s.status in ("success", "failed") for s in self.module_states.values())

        if failed_modules:
            lines.append(f"**⚠️ Paused: `{'`, `'.join(failed_modules)}` failed**")
        elif all_done:
            lines.append(f"**✅ All {total} modules synced successfully**")
        else:
            lines.append(f"**Status:** In Progress ({completed}/{total} complete)")

        return "\n".join(lines)



def _format_duration(start: Optional[float], end: Optional[float]) -> str:
    """Format a duration from start/end timestamps."""
    if start is None or end is None:
        return "-"
    seconds = int(end - start)
    if seconds < 60:
        return f"{seconds}s"
    minutes = seconds // 60
    remaining = seconds % 60
    return f"{minutes}m{remaining}s"
