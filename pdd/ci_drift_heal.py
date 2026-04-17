from __future__ import annotations

import argparse
import csv
import os
import subprocess
import sys
import tempfile
from dataclasses import dataclass
from pathlib import Path
from typing import Dict, List, Optional, Tuple

from rich.console import Console
from rich.table import Table

console = Console()
_ROLLBACK_PATHS = (".pdd/meta", "project_dependencies.csv")


def _get_git_changed_files(diff_base: str) -> set:
    """Return the set of file paths changed between diff_base and HEAD.

    Args:
        diff_base: Git diff base reference (e.g. "origin/main...HEAD" or "HEAD~1").

    Returns:
        Set of changed file paths (relative to repo root), or empty set on failure.
    """
    try:
        result = subprocess.run(
            ["git", "diff", "--name-only", diff_base],
            capture_output=True,
            text=True,
            timeout=30,
        )
        if result.returncode == 0:
            return {line.strip() for line in result.stdout.splitlines() if line.strip()}
        return set()
    except Exception:
        return set()


@dataclass
class DriftInfo:
    """Represents a detected drift for a single module."""

    basename: str
    language: str
    operation: str  # 'update' (prompt stale) or 'example' (example stale)
    reason: str
    code_path: Optional[str] = None  # resolved code file path for pdd update


@dataclass
class HealResult:
    """Result of a healing attempt for a single module."""

    basename: str
    success: bool
    cost: float = 0.0
    error: str = ""


def _build_ci_env(cost_csv_path: str) -> Dict[str, str]:
    """Build environment dict for subprocess calls in CI/headless mode."""
    env = os.environ.copy()
    env["PDD_FORCE"] = "1"
    env["CI"] = "1"
    env["NO_COLOR"] = "1"
    env["PDD_OUTPUT_COST_PATH"] = cost_csv_path
    env["PDD_FORCE_LOCAL"] = "1"
    # Disable local models (LM Studio) that hang connecting to localhost.
    # Set a fake required API key so pdd's model selection skips them
    # (empty api_key = "no auth needed" = always selected as cheapest).
    env["PDD_SKIP_LOCAL_MODELS"] = "1"
    # If a heal subprocess times out or fails in CI, restore tracked metadata/cache
    # files so the repo doesn't stay stuck in a half-mutated state.
    env["PDD_RESTORE_PROTECTED_PATHS_ON_FAILURE"] = "1"
    return env


def _capture_rollback_state(cmd: List[str], env: Dict[str, str]) -> Optional[bool]:
    """Return True when protected paths started clean and should be restorable.

    We only attempt rollback for `pdd update` / `pdd sync` subprocesses launched by
    the CI auto-heal wrapper, and only when `.pdd/meta` plus `project_dependencies.csv`
    were pristine before the command started.
    """
    if env.get("PDD_RESTORE_PROTECTED_PATHS_ON_FAILURE") != "1":
        return None
    if len(cmd) < 2 or cmd[0] != "pdd" or cmd[1] not in {"sync", "update"}:
        return None

    try:
        status_result = subprocess.run(
            ["git", "status", "--porcelain", "--", *_ROLLBACK_PATHS],
            capture_output=True,
            text=True,
            timeout=30,
        )
    except Exception:
        return None

    if status_result.returncode != 0:
        return None

    return not bool((status_result.stdout or "").strip())


def _restore_protected_paths(rollback_state: Optional[bool], label: str) -> None:
    """Restore tracked metadata/cache files when the heal started from a clean state."""
    if rollback_state is not True:
        return

    try:
        restore_result = subprocess.run(
            ["git", "restore", "--source=HEAD", "--", *_ROLLBACK_PATHS],
            capture_output=True,
            text=True,
            timeout=30,
        )
        if restore_result.returncode != 0:
            # Fallback for older Git versions or unusual restore failures.
            restore_result = subprocess.run(
                ["git", "checkout", "--", *_ROLLBACK_PATHS],
                capture_output=True,
                text=True,
                timeout=30,
            )
        if restore_result.returncode == 0:
            console.print(
                "[yellow]↩ Restored tracked .pdd/meta and "
                f"project_dependencies.csv after {label} failed[/yellow]"
            )
            return
        stderr_snippet = (restore_result.stderr or "").strip()[-500:]
        if stderr_snippet:
            console.print(
                "[yellow]⚠ Failed to restore protected files after "
                f"{label}: {stderr_snippet}[/yellow]"
            )
    except Exception as exc:
        console.print(
            "[yellow]⚠ Failed to restore protected files after "
            f"{label}: {exc}[/yellow]"
        )


def _parse_cost_from_csv(csv_path: str) -> float:
    """Parse cumulative cost from a PDD cost CSV file.

    Uses the same CSV format as pdd.agentic_sync_runner._parse_cost_from_csv.
    Returns total cost found in the CSV, or 0.0 if file doesn't exist or is empty.
    """
    path = Path(csv_path)
    if not path.exists():
        return 0.0
    total = 0.0
    try:
        with open(path, newline="", encoding="utf-8") as f:
            reader = csv.DictReader(f)
            for row in reader:
                cost_val = row.get("cost") or row.get("total_cost") or "0"
                try:
                    total += float(cost_val)
                except (ValueError, TypeError):
                    pass
    except Exception:
        return 0.0
    return total


def detect_drift(modules: Optional[List[str]] = None, diff_base: Optional[str] = None) -> Tuple[List[DriftInfo], List[DriftInfo]]:
    """Detect prompt and example drift across PDD modules.

    Args:
        modules: Optional list of basenames to limit detection scope.
                 If None, scans all modules discovered via discover_prompt_files().
        diff_base: Optional git diff base (e.g. "origin/main...HEAD"). When provided,
                   enables git-based reclassification: if sync_determine_operation returns
                   a non-'update' operation but git shows the code file changed while the
                   prompt didn't, the drift is reclassified as 'update' (prompt stale).
                   This fixes detection in CI where fingerprints are absent.

    Returns:
        Tuple of (prompt_drifts, example_drifts) where each is a list of DriftInfo.
        prompt_drifts have operation=='update', example_drifts have operation=='example'.
    """
    from pdd.operation_log import infer_module_identity
    from pdd.sync_determine_operation import get_pdd_file_paths, sync_determine_operation
    from pdd.user_story_tests import discover_prompt_files

    prompt_files = discover_prompt_files()

    prompt_drifts: List[DriftInfo] = []
    example_drifts: List[DriftInfo] = []
    seen_basenames: set = set()

    # Pre-fetch git changed files once (not per-module) for reclassification
    git_changed: Optional[set] = None
    if diff_base:
        git_changed = _get_git_changed_files(diff_base)

    for prompt_path in prompt_files:
        try:
            basename, language = infer_module_identity(str(prompt_path))
        except Exception as e:
            console.print(
                f"[yellow]⚠ Could not infer identity for {prompt_path}: {e}[/yellow]"
            )
            continue

        if basename is None or language is None:
            continue

        # Scope control: skip modules not in the requested list
        if modules is not None and basename not in modules:
            continue

        seen_basenames.add(basename)

        try:
            decision = sync_determine_operation(
                basename, language, target_coverage=90.0, log_mode=True
            )
        except Exception as e:
            console.print(
                f"[yellow]⚠ Error analyzing {basename} ({language}): {e}[/yellow]"
            )
            continue

        # Skip modules that are fully synced or in error state
        if decision.operation in ("nothing", "all_synced", "error"):
            continue

        # Resolve code file path for update operations
        code_path = None
        if decision.operation == "update":
            try:
                paths = get_pdd_file_paths(basename, language)
                code_file = paths.get("code")
                if code_file and code_file.exists():
                    code_path = str(code_file)
            except Exception:
                pass

        # Git-based reclassification: In CI (clean checkout without fingerprints),
        # sync_determine_operation always returns 'auto-deps' or 'generate' because
        # there is no fingerprint to compare code hashes against.  When we have git
        # history, we can detect the actual drift direction: if the code file changed
        # but the prompt file did NOT, the code is ahead and the prompt needs updating.
        if decision.operation != "update" and git_changed is not None:
            try:
                paths = get_pdd_file_paths(basename, language)
                # get_pdd_file_paths returns absolute Path objects but git diff
                # returns repo-relative paths.  Convert to relative for comparison.
                repo_root = Path.cwd()
                code_file_abs = paths.get("code")
                prompt_file_abs = paths.get("prompt")

                def _to_relative(p: Optional[Path]) -> str:
                    if not p:
                        return ""
                    try:
                        return str(p.relative_to(repo_root))
                    except ValueError:
                        return str(p)

                code_file_path = _to_relative(code_file_abs)
                prompt_file_path = _to_relative(prompt_file_abs)

                code_changed = code_file_path in git_changed
                prompt_changed = prompt_file_path in git_changed

                if code_changed and not prompt_changed:
                    console.print(
                        f"[blue]↑ Reclassifying {basename}: code changed but prompt "
                        f"unchanged → prompt (update) drift[/blue]"
                    )
                    code_path = str(code_file_abs) if code_file_abs else code_file_path
                    decision = type(decision)(
                        operation="update",
                        reason="Code changed but prompt unchanged (git-based detection)",
                        confidence=getattr(decision, "confidence", 0.85),
                        estimated_cost=getattr(decision, "estimated_cost", 0.25),
                        details=getattr(decision, "details", {}),
                    )
            except Exception as e:
                console.print(
                    f"[yellow]⚠ Git reclassification failed for {basename}: {e}[/yellow]"
                )

        if decision.operation == "update":
            prompt_drifts.append(
                DriftInfo(
                    basename=basename,
                    language=language,
                    operation="update",
                    reason=getattr(decision, "reason", "Prompt stale"),
                    code_path=code_path,
                )
            )
        else:
            # All other drift types (example, verify, generate, test, crash,
            # auto-deps, etc.) are handled via pdd sync
            example_drifts.append(
                DriftInfo(
                    basename=basename,
                    language=language,
                    operation="example",
                    reason=getattr(decision, "reason", "Needs sync"),
                )
            )

    # Detect code files without prompts: these need `pdd update` to generate
    # the prompt and complete the dev unit.
    if modules is not None:
        _LANG_EXTENSIONS = {
            ".py": "python", ".ts": "typescript", ".tsx": "typescript",
            ".js": "javascript", ".jsx": "javascript", ".go": "go",
            ".rs": "rust", ".java": "java", ".rb": "ruby",
            ".sh": "bash", ".bash": "bash",
        }
        for basename in modules:
            if basename in seen_basenames:
                continue
            # No prompt found for this basename — look for a code file
            for ext, language in _LANG_EXTENSIONS.items():
                candidates = list(Path(".").rglob(f"{basename}{ext}"))
                # Filter out test files, examples, and hidden dirs
                candidates = [
                    c for c in candidates
                    if not any(p.startswith(".") for p in c.parts)
                    and "test" not in c.name.lower().split(basename.lower())[0]
                    and "example" not in c.name.lower()
                ]
                if candidates:
                    code_path = str(candidates[0])
                    prompt_drifts.append(
                        DriftInfo(
                            basename=basename,
                            language=language,
                            operation="update",
                            reason="Code exists without prompt — needs pdd update",
                            code_path=code_path,
                        )
                    )
                    seen_basenames.add(basename)
                    break

    return prompt_drifts, example_drifts


def _print_drift_table(
    prompt_drifts: List[DriftInfo], example_drifts: List[DriftInfo]
) -> None:
    """Print a summary table of detected drift."""
    table = Table(title="Detected Drift Summary")
    table.add_column("Module", style="cyan")
    table.add_column("Language", style="blue")
    table.add_column("Drift Type", style="magenta")
    table.add_column("Reason", style="white")

    for drift in prompt_drifts:
        table.add_row(drift.basename, drift.language, "prompt (update)", drift.reason)
    for drift in example_drifts:
        table.add_row(drift.basename, drift.language, "example (sync)", drift.reason)

    console.print(table)


def _run_pdd_command(cmd: List[str], env: Dict[str, str], label: str) -> bool:
    """Run a pdd subprocess command, returning True on success."""
    console.print(f"[blue]⟳ {label}: {' '.join(cmd)}[/blue]")
    rollback_state = _capture_rollback_state(cmd, env)
    try:
        # pdd sync summarizes every context file before healing and can route
        # to slow-path models (e.g. Claude Opus via Vertex) on large repos.
        # 20 min covers Opus summarization; GCB step-level timeout still caps
        # total runaway at 30 min.
        result = subprocess.run(
            cmd,
            env=env,
            capture_output=True,
            text=True,
            timeout=1200,
        )
        if result.returncode == 0:
            console.print(f"[green]✓ {label} succeeded[/green]")
            return True
        else:
            stderr_snippet = (result.stderr or "").strip()[-500:]
            console.print(f"[red]✗ {label} failed (exit code {result.returncode})[/red]")
            if stderr_snippet:
                console.print(f"[dim]{stderr_snippet}[/dim]")
            _restore_protected_paths(rollback_state, label)
            return False
    except subprocess.TimeoutExpired as e:
        console.print(f"[red]✗ {label} timed out[/red]")
        if e.stdout:
            console.print(f"[dim]stdout (last 1000 chars): {e.stdout[-1000:]}[/dim]")
        if e.stderr:
            console.print(f"[dim]stderr (last 1000 chars): {e.stderr[-1000:]}[/dim]")
        _restore_protected_paths(rollback_state, label)
        return False
    except FileNotFoundError:
        console.print(
            "[red]✗ 'pdd' command not found. Ensure pdd is installed and on PATH.[/red]"
        )
        return False
    except Exception as e:
        console.print(f"[red]✗ {label} error: {e}[/red]")
        _restore_protected_paths(rollback_state, label)
        return False


def heal_module(drift: DriftInfo, env: Dict[str, str]) -> bool:
    """Heal a single drifted module by running the appropriate pdd command.

    For 'update' drift (code changed, prompt stale), runs pdd update first
    to sync the prompt from code, then pdd sync to regenerate the example
    from the updated prompt — all in one pass.

    Args:
        drift: DriftInfo describing the drift to heal.
        env: Environment variables dict for the subprocess.

    Returns:
        True if healing succeeded, False otherwise.
    """
    if drift.operation == "update":
        # Step 1: Update the prompt from code
        if drift.code_path:
            update_cmd = ["pdd", "update", drift.code_path]
        else:
            update_cmd = ["pdd", "update"]

        if not _run_pdd_command(update_cmd, env, f"Healing {drift.basename} (update)"):
            return False

        # Step 2: Sync example from the now-updated prompt so everything is
        # consistent in a single CI pass (no second cycle needed).
        sync_cmd = ["pdd", "sync", drift.basename]
        if not _run_pdd_command(sync_cmd, env, f"Syncing {drift.basename} (example)"):
            # Update succeeded but sync failed — still count as partial success
            # so the prompt update gets committed.
            console.print(
                f"[yellow]⚠ Prompt updated but example sync failed for "
                f"{drift.basename} — example may need a follow-up sync[/yellow]"
            )
        return True

    elif drift.operation == "example":
        return _run_pdd_command(
            ["pdd", "sync", drift.basename], env, f"Healing {drift.basename} (sync)"
        )
    else:
        console.print(
            f"[red]✗ Unknown operation '{drift.operation}' for {drift.basename}[/red]"
        )
        return False


def commit_and_push(healed_modules: List[str], skip_ci: bool = False) -> bool:
    """Stage, commit, and push healed changes.

    Args:
        healed_modules: List of module basenames that were healed.
        skip_ci: If True, prepend [skip ci] to commit message.

    Returns:
        True if commit and push succeeded, False otherwise.
    """
    if not healed_modules:
        console.print("[yellow]No modules to commit.[/yellow]")
        return True

    module_list = ", ".join(healed_modules)
    commit_msg = f"chore: auto-heal prompt/example drift for {module_list}"
    if skip_ci:
        commit_msg = f"[skip ci] {commit_msg}"

    # Stage all changes. CI runs on a clean checkout so -A is safe, and healing
    # may create new files (e.g. a missing example) that -u would miss.
    try:
        subprocess.run(
            ["git", "add", "-A"],
            check=False,
            capture_output=True,
            text=True,
        )
    except Exception as e:
        console.print(f"[yellow]⚠ Could not stage changes: {e}[/yellow]")

    # Check if there are staged changes
    try:
        diff_result = subprocess.run(
            ["git", "diff", "--cached", "--quiet"],
            capture_output=True,
            text=True,
        )
        if diff_result.returncode == 0:
            console.print("[yellow]No staged changes to commit.[/yellow]")
            return True
    except Exception:
        pass

    # Commit
    try:
        commit_result = subprocess.run(
            ["git", "commit", "-m", commit_msg],
            capture_output=True,
            text=True,
        )
        if commit_result.returncode != 0:
            stderr = (commit_result.stderr or "").strip()
            console.print(f"[red]✗ Git commit failed: {stderr}[/red]")
            return False
        console.print(f"[green]✓ Committed: {commit_msg}[/green]")
    except Exception as e:
        console.print(f"[red]✗ Git commit error: {e}[/red]")
        return False

    # Push to current branch
    try:
        push_result = subprocess.run(
            ["git", "push"],
            capture_output=True,
            text=True,
        )
        if push_result.returncode != 0:
            stderr = (push_result.stderr or "").strip()
            console.print(f"[red]✗ Git push failed: {stderr}[/red]")
            return False
        console.print("[green]✓ Pushed to remote[/green]")
    except Exception as e:
        console.print(f"[red]✗ Git push error: {e}[/red]")
        return False

    return True


def main(
    modules: Optional[List[str]] = None,
    budget_cap: Optional[float] = None,
    skip_ci: bool = False,
    diff_base: Optional[str] = None,
) -> int:
    """Main entry point for drift detection and auto-healing.

    Args:
        modules: Optional list of basenames to limit scope.
        budget_cap: Optional budget cap in dollars for LLM healing costs.
        skip_ci: If True, prepend [skip ci] to commit message.
        diff_base: Optional git diff base for git-based drift reclassification.

    Returns:
        0 on success (including no drift), 1 on any failure.
    """
    console.print("[bold]🔍 PDD Drift Detection & Auto-Heal[/bold]\n")

    if modules:
        console.print(f"Scope limited to modules: {', '.join(modules)}")
    if budget_cap is not None:
        console.print(f"Budget cap: ${budget_cap:.2f}")

    # --- Detection Phase ---
    console.print("\n[bold]Phase 1: Detecting drift...[/bold]")
    try:
        prompt_drifts, example_drifts = detect_drift(modules, diff_base=diff_base)
    except Exception as e:
        console.print(f"[red]✗ Detection failed: {e}[/red]")
        return 1

    all_drifts = prompt_drifts + example_drifts

    if not all_drifts:
        console.print("[green]✓ No drift detected. All modules are synchronized.[/green]")
        return 0

    _print_drift_table(prompt_drifts, example_drifts)
    console.print(
        f"\nFound [bold]{len(all_drifts)}[/bold] drifted module(s): "
        f"{len(prompt_drifts)} prompt, {len(example_drifts)} example\n"
    )

    # --- Healing Phase ---
    console.print("[bold]Phase 2: Healing drifted modules...[/bold]\n")

    # Create temp CSV for cost tracking
    cost_csv_fd, cost_csv_path = tempfile.mkstemp(suffix=".csv", prefix="pdd_cost_")
    os.close(cost_csv_fd)

    try:
        env = _build_ci_env(cost_csv_path)
        cumulative_cost = 0.0
        healed_modules: List[str] = []
        failed_modules: List[str] = []
        skipped_modules: List[str] = []
        any_failure = False

        for drift in all_drifts:
            # Budget check before each heal
            if budget_cap is not None and cumulative_cost >= budget_cap:
                console.print(
                    f"[yellow]⚠ Budget cap (${budget_cap:.2f}) reached. "
                    f"Skipping {drift.basename}[/yellow]"
                )
                skipped_modules.append(drift.basename)
                continue

            # Clear cost CSV before each operation to get per-operation cost
            Path(cost_csv_path).write_text("", encoding="utf-8")

            success = heal_module(drift, env)

            # Parse cost from this operation
            operation_cost = _parse_cost_from_csv(cost_csv_path)
            cumulative_cost += operation_cost

            if operation_cost > 0:
                console.print(
                    f"  Cost: ${operation_cost:.4f} "
                    f"(cumulative: ${cumulative_cost:.4f})"
                )

            if success:
                healed_modules.append(drift.basename)
            else:
                failed_modules.append(drift.basename)
                any_failure = True

        # Print skipped modules warning
        if skipped_modules:
            console.print(
                f"\n[yellow]⚠ Budget exceeded. Skipped modules: "
                f"{', '.join(skipped_modules)}[/yellow]"
            )

    finally:
        # Clean up temp CSV
        try:
            os.unlink(cost_csv_path)
        except OSError:
            pass

    # --- Summary ---
    console.print(f"\n[bold]Healing Summary:[/bold]")
    console.print(f"  Healed:  {len(healed_modules)}")
    console.print(f"  Failed:  {len(failed_modules)}")
    console.print(f"  Skipped: {len(skipped_modules)}")
    console.print(f"  Total cost: ${cumulative_cost:.4f}")

    # --- Commit Phase ---
    if healed_modules:
        console.print("\n[bold]Phase 3: Committing changes...[/bold]\n")
        commit_success = commit_and_push(healed_modules, skip_ci)
        if not commit_success:
            any_failure = True
    else:
        console.print("\n[yellow]No modules healed — skipping commit phase.[/yellow]")

    if any_failure:
        if skip_ci:
            # Push-to-main mode: heal failures are advisory, not blocking
            console.print("\n[yellow]⚠ Completed with failures (non-blocking on push to main).[/yellow]")
            return 0
        console.print("\n[red]✗ Completed with failures.[/red]")
        return 1

    console.print("\n[green]✓ Drift heal completed successfully.[/green]")
    return 0


def _parse_args(argv: Optional[List[str]] = None) -> argparse.Namespace:
    """Parse CLI arguments."""
    parser = argparse.ArgumentParser(
        description="PDD Drift Detection & Auto-Heal CI Script",
        prog="drift_heal",
    )
    parser.add_argument(
        "--modules",
        nargs="*",
        default=None,
        help="Space-separated list of module basenames to check. "
        "If omitted, all discovered modules are scanned.",
    )
    parser.add_argument(
        "--budget-cap",
        type=float,
        default=None,
        help="Maximum LLM cost in dollars for healing operations.",
    )
    parser.add_argument(
        "--skip-ci",
        action="store_true",
        default=False,
        help="Prepend [skip ci] to the commit message.",
    )
    parser.add_argument(
        "--diff-base",
        type=str,
        default=None,
        help="Git diff base reference (e.g. 'origin/main...HEAD') for detecting "
        "drift direction. When set, code-changed-but-prompt-unchanged modules "
        "are reclassified as prompt (update) drift instead of example (sync).",
    )
    args = parser.parse_args(argv)

    # Expand comma-separated module values so that both
    # --modules "auth,api" and --modules auth api work correctly.
    if args.modules is not None:
        expanded: List[str] = []
        for m in args.modules:
            expanded.extend(part for part in m.split(",") if part)
        args.modules = expanded

    return args


if __name__ == "__main__":
    args = _parse_args()
    exit_code = main(
        modules=args.modules,
        budget_cap=args.budget_cap,
        skip_ci=args.skip_ci,
        diff_base=args.diff_base,
    )
    sys.exit(exit_code)
