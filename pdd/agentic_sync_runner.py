"""
Async sync runner: parallel module sync with dependency-aware scheduling.

Manages concurrent `pdd sync` subprocesses, respects dependency ordering,
updates a live GitHub issue comment with progress, and pauses on failure.
"""
from __future__ import annotations

import csv
import json
import os
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

# Maximum concurrent syncs
MAX_WORKERS = 4
# Per-module timeout in seconds
MODULE_TIMEOUT = 900


@dataclass
class ModuleState:
    """Tracks the execution state of a single module sync."""

    status: str = "pending"  # pending, running, success, failed
    start_time: Optional[float] = None
    end_time: Optional[float] = None
    cost: float = 0.0
    error: Optional[str] = None


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

    # Map prompt filename -> basename
    filename_to_basename: Dict[str, str] = {}
    for entry in arch:
        filename = entry.get("filename", "")
        basename = extract_module_from_include(filename)
        if basename:
            filename_to_basename[filename] = basename

    target_set = set(target_basenames)

    # Build graph
    graph: Dict[str, List[str]] = {}
    for entry in arch:
        basename = filename_to_basename.get(entry.get("filename", ""))
        if basename and basename in target_set:
            deps = []
            for dep_filename in entry.get("dependencies", []):
                dep_basename = filename_to_basename.get(dep_filename)
                if dep_basename and dep_basename in target_set and dep_basename != basename:
                    deps.append(dep_basename)
            graph[basename] = deps

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
    ):
        self.basenames = basenames
        self.dep_graph = dep_graph
        self.sync_options = sync_options
        self.github_info = github_info
        self.quiet = quiet
        self.verbose = verbose
        self.project_root = Path.cwd()

        self.module_states: Dict[str, ModuleState] = {
            b: ModuleState() for b in basenames
        }
        self.failed = False
        self.comment_id: Optional[int] = None
        self.lock = threading.Lock()

    def run(self) -> Tuple[bool, str, float]:
        """
        Run all syncs respecting dependencies.

        Returns:
            Tuple of (all_success, summary_message, total_cost).
        """
        if not self.basenames:
            return True, "No modules to sync", 0.0

        self._update_github_comment()

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
                    for basename in ready:
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
            return False, msg, total_cost
        elif pending:
            msg = f"Succeeded: {succeeded}. Skipped (blocked): {pending}."
            return False, msg, total_cost
        else:
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
        """Record the result of a module sync."""
        with self.lock:
            state = self.module_states[basename]
            state.status = "success" if success else "failed"
            state.end_time = time.time()
            state.cost = cost
            if not success:
                state.error = error

    def _sync_one_module(self, basename: str) -> Tuple[bool, float, str]:
        """
        Run pdd sync for a single module as a subprocess.

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
        if self.sync_options.get("agentic"):
            cmd.append("--agentic")
        if self.sync_options.get("no_steer"):
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
        env["TERM"] = "dumb"

        if not self.quiet:
            console.print(f"[blue]Starting sync: {basename}[/blue]")

        try:
            result = subprocess.run(
                cmd,
                capture_output=True,
                text=True,
                cwd=str(self.project_root),
                env=env,
                timeout=MODULE_TIMEOUT,
            )
        except subprocess.TimeoutExpired:
            return False, 0.0, f"Timeout after {MODULE_TIMEOUT}s"
        except Exception as e:
            return False, 0.0, str(e)
        finally:
            # Parse cost regardless of outcome
            pass

        cost = _parse_cost_from_csv(cost_file.name)

        # Clean up cost file
        try:
            os.unlink(cost_file.name)
        except OSError:
            pass

        # Detect success
        success = result.returncode == 0
        if success:
            for line in result.stdout.splitlines():
                if "Overall status:" in line and "Failed" in line:
                    success = False
                    break

        if not self.quiet:
            status_str = "success" if success else "FAILED"
            console.print(f"[{'green' if success else 'red'}]Sync {basename}: {status_str}[/{'green' if success else 'red'}]")

        error = ""
        if not success:
            # Combine stderr and relevant stdout for error reporting
            error = result.stderr or ""
            if not error:
                # Look for error lines in stdout
                error_lines = [
                    line for line in result.stdout.splitlines()
                    if "error" in line.lower() or "failed" in line.lower() or "traceback" in line.lower()
                ]
                error = "\n".join(error_lines[-20:]) if error_lines else f"Exit code {result.returncode}"

        return success, cost, error

    def _update_github_comment(self) -> None:
        """Create or update a GitHub issue comment with current progress."""
        if not self.github_info:
            return

        owner = self.github_info["owner"]
        repo = self.github_info["repo"]
        issue_number = self.github_info["issue_number"]

        body = self._build_comment_body(issue_number)

        try:
            if self.comment_id is None:
                # Create new comment
                from .agentic_change import _run_gh_command

                ok, response = _run_gh_command([
                    "api", f"repos/{owner}/{repo}/issues/{issue_number}/comments",
                    "-X", "POST", "-f", f"body={body}",
                ])
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
                ])
        except Exception:
            pass  # Don't break sync for comment failures

    def _build_comment_body(self, issue_number: int) -> str:
        """Build the markdown comment body showing sync progress."""
        lines = [
            "## PDD Agentic Sync Progress",
            f"Issue: #{issue_number}",
            "",
            "| Module | Status | Duration | Cost |",
            "|--------|--------|----------|------|",
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
                elif state.status == "failed":
                    icon = "❌ Failed"
                    completed += 1
                    duration = _format_duration(state.start_time, state.end_time)
                    cost_str = f"${state.cost:.2f}"
                elif state.status == "running":
                    icon = "🔄 Running"
                    duration = _format_duration(state.start_time, time.time())
                    cost_str = "-"
                else:
                    icon = "⏳ Pending"
                    duration = "-"
                    cost_str = "-"

                lines.append(f"| {basename} | {icon} | {duration} | {cost_str} |")

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
