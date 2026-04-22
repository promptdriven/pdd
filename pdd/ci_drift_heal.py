from __future__ import annotations

import argparse
import csv
import math
import os
import re
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

# Change-magnitude gate threshold. Motivation: PR gltanaka/pdd#1187 autohealed
# a 1-line code fix (`ad98ea17`) into a 176-line prompt rewrite — a 1:176 ratio.
# Typical healthy prompt-update ratios sit between 1:1 and 2:1; a cap at 5×
# catches pathological cases cleanly without blocking legitimate updates where
# a small refactor rightly touches multiple prompt sections. Override via
# the `PDD_HEAL_PROMPT_CHURN_MAX_RATIO` env var in CI if needed.
_HEAL_PROMPT_CHURN_MAX_RATIO = 5.0

# Optional operator override for temporarily skipping `pdd sync` paths in CI
# auto-heal. Unset env means "skip nothing"; set
# PDD_HEAL_SYNC_SKIP_MODULES=mod1,mod2 to opt modules out if a sync path
# regresses and needs a short-lived operational bypass.


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
    prompt_path: Optional[str] = None  # resolved prompt file path for churn gate
    diff_base: Optional[str] = None  # git diff base, used by change-magnitude gate


@dataclass
class HealResult:
    """Result of a healing attempt for a single module."""

    basename: str
    success: bool
    cost: float = 0.0
    error: str = ""


class PromptRevertError(RuntimeError):
    """Raised when a failed heal cannot safely revert prompt edits."""


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


def _get_heal_sync_skip_modules() -> set[str]:
    """Return modules whose `pdd sync` step should be skipped in CI auto-heal.

    Unset or empty env means "skip nothing".
    """
    raw = os.environ.get("PDD_HEAL_SYNC_SKIP_MODULES", "")
    return {name.strip() for name in raw.split(",") if name.strip()}


def _get_heal_sync_skip_reason(basename: str) -> Optional[str]:
    """Return a human-readable skip reason for timeout-prone sync modules."""
    if basename not in _get_heal_sync_skip_modules():
        return None
    return f"{basename} is listed in PDD_HEAL_SYNC_SKIP_MODULES"


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
            resolved_prompt_path: Optional[str] = None
            try:
                paths = get_pdd_file_paths(basename, language)
                prompt_file_abs = paths.get("prompt")
                if prompt_file_abs is not None:
                    resolved_prompt_path = str(prompt_file_abs)
            except Exception:
                resolved_prompt_path = None
            prompt_drifts.append(
                DriftInfo(
                    basename=basename,
                    language=language,
                    operation="update",
                    reason=getattr(decision, "reason", "Prompt stale"),
                    code_path=code_path,
                    prompt_path=resolved_prompt_path,
                    diff_base=diff_base,
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


def _numstat_line_counts(diff_args: List[str]) -> Optional[Tuple[int, int]]:
    """Return (added, deleted) line counts from `git diff --numstat <args>`.

    Returns None if the diff command fails or produces no rows. When multiple
    files appear in the diff, the counts are summed. A binary-diff row
    (indicated by "-\t-") contributes zero.
    """
    try:
        result = subprocess.run(
            ["git", "diff", "--numstat"] + diff_args,
            capture_output=True,
            text=True,
            timeout=30,
        )
        if result.returncode != 0:
            return None
        added = 0
        deleted = 0
        saw_row = False
        for line in result.stdout.splitlines():
            parts = line.strip().split("\t")
            if len(parts) < 2:
                continue
            a_str, d_str = parts[0], parts[1]
            if a_str == "-" or d_str == "-":
                saw_row = True
                continue
            try:
                added += int(a_str)
                deleted += int(d_str)
                saw_row = True
            except ValueError:
                continue
        if not saw_row:
            return None
        return (added, deleted)
    except Exception:
        return None


def _enforce_prompt_churn_gate(drift: DriftInfo) -> bool:
    """Check that the prompt churn is not wildly larger than the code churn.

    After `pdd update` runs, the prompt file is modified in the working tree
    (not yet committed). We compare `git diff --numstat HEAD -- <prompt_path>`
    (prompt churn) against `git diff --numstat <diff_base> -- <code_path>`
    (code churn that motivated the heal). If prompt-churn / code-churn
    exceeds `_HEAL_PROMPT_CHURN_MAX_RATIO`, we revert the prompt file and
    return False so the caller treats the heal as failed.

    This is a safety net for cases where the LLM rewrites far more of the
    prompt than the code change warrants (see PR gltanaka/pdd#1187).
    Returns True when the gate passes or when we cannot measure (missing
    paths, git errors) — in the unmeasurable case we prefer to let the
    healthier structural-invariant validator be the gatekeeper.
    """
    if not drift.prompt_path or not drift.code_path or not drift.diff_base:
        return True

    ratio_cap_str = os.environ.get("PDD_HEAL_PROMPT_CHURN_MAX_RATIO")
    try:
        ratio_cap = float(ratio_cap_str) if ratio_cap_str else _HEAL_PROMPT_CHURN_MAX_RATIO
    except ValueError:
        ratio_cap = _HEAL_PROMPT_CHURN_MAX_RATIO

    prompt_counts = _numstat_line_counts(["HEAD", "--", drift.prompt_path])
    code_counts = _numstat_line_counts([drift.diff_base, "--", drift.code_path])

    if prompt_counts is None or code_counts is None:
        return True

    prompt_churn = prompt_counts[0] + prompt_counts[1]
    code_churn = max(1, code_counts[0] + code_counts[1])
    ratio = prompt_churn / code_churn

    if ratio <= ratio_cap:
        return True

    console.print(
        f"[red]✗ Prompt churn gate tripped for {drift.basename}: "
        f"prompt changed {prompt_churn} lines vs code {code_churn} lines "
        f"(ratio {ratio:.1f} > cap {ratio_cap:.1f}).[/red]\n"
        f"[red]  Rewrite was likely destructive — see PR gltanaka/pdd#1187. "
        f"Reverting {drift.prompt_path} and skipping this module.[/red]"
    )
    _revert_prompt_file(drift)
    return False


# Regexes used by the structural-invariants validator. Compiled once at module
# import time so the gate adds negligible overhead per heal.
_INCLUDE_TAG_RE = re.compile(r"<include(?:-many)?>")
_PDD_OPEN_TAG_RE = re.compile(r"<pdd\.[A-Za-z_][A-Za-z0-9_]*>")
_PERCENT_MARKER_RE = re.compile(r"^%\s", re.MULTILINE)
_FENCED_BLOCK_RE = re.compile(r"```[^\n]*\n.*?\n```", re.DOTALL)

# Env var for selectively disabling individual invariants. Comma-separated
# list of invariant names. Motivation: invariant #4 (fenced blocks byte-
# identical) is the strictest — it blocks legitimate refactors where an
# example's API signature inside a fenced block needs to change. Without
# an escape hatch the only way out would be a code change here. The other
# invariants are already soft (counts or subset checks) but expose them
# for uniformity.
_VALID_SKIPPABLE_INVARIANTS = frozenset({
    "include",          # skip invariant #1 (<include>/<include-many> count)
    "pdd_tags",         # skip invariant #2 (<pdd.*> prefix preservation)
    "percent_markers",  # skip invariant #3 (% section marker threshold)
    "fenced_blocks",    # skip invariant #4 (fenced block byte-identity)
})


def _get_skipped_invariants() -> set:
    """Return the set of invariant names to skip, parsed from env var.

    Reads `PDD_HEAL_INVARIANTS_SKIP` as a comma-separated list. Unknown
    names are logged and dropped rather than raising, so a typo in CI
    config doesn't break the whole heal. Empty / unset env → empty set
    (all invariants enforced).
    """
    raw = os.environ.get("PDD_HEAL_INVARIANTS_SKIP", "")
    if not raw.strip():
        return set()
    requested = {s.strip() for s in raw.split(",") if s.strip()}
    unknown = requested - _VALID_SKIPPABLE_INVARIANTS
    if unknown:
        console.print(
            f"[yellow]⚠ Unknown invariant names in "
            f"PDD_HEAL_INVARIANTS_SKIP, ignoring: {sorted(unknown)}. "
            f"Valid names: {sorted(_VALID_SKIPPABLE_INVARIANTS)}.[/yellow]"
        )
    return requested & _VALID_SKIPPABLE_INVARIANTS


def _git_repo_relative_path(file_path: str) -> Optional[str]:
    """Return a git-friendly repo-relative path for `file_path`.

    Absolute paths from get_pdd_file_paths() work for filesystem IO but not for
    `git checkout HEAD -- <path>` in Cloud Build. Convert absolute paths to a
    repo-relative POSIX form while leaving already-relative paths untouched.
    Returns None when the repo root cannot be determined or the path is outside
    the repo.
    """
    try:
        path = Path(file_path)
        if not path.is_absolute():
            return path.as_posix()

        repo_root_proc = subprocess.run(
            ["git", "rev-parse", "--show-toplevel"],
            capture_output=True,
            text=True,
            timeout=10,
        )
        if repo_root_proc.returncode != 0:
            return None

        repo_root = Path(repo_root_proc.stdout.strip()).resolve()
        return path.resolve().relative_to(repo_root).as_posix()
    except Exception:
        return None


def _git_show_prompt_at_head(prompt_path: str) -> Optional[str]:
    """Return the committed HEAD content of `prompt_path`, or None on failure.

    `git show HEAD:<path>` requires a repo-relative path with forward slashes;
    absolute paths (which is what DriftInfo.prompt_path holds, since
    get_pdd_file_paths returns absolute Paths) are rejected by git. Resolve
    the path against the repo root first, then hand the relative form to git.
    """
    try:
        rel_str = _git_repo_relative_path(prompt_path)
        if rel_str is None:
            return None
        show_proc = subprocess.run(
            ["git", "show", f"HEAD:{rel_str}"],
            capture_output=True,
            text=True,
            timeout=30,
        )
        if show_proc.returncode != 0:
            return None
        return show_proc.stdout
    except Exception:
        return None


def _enforce_structural_invariants(drift: DriftInfo) -> bool:
    """Verify that `pdd update` did not strip known structural elements.

    Path-agnostic post-heal check: runs regardless of whether the legacy
    two-stage `update_prompt()` or the agentic path produced the rewrite.
    Pulls the pre-heal content from `git show HEAD:<prompt_path>` and
    compares it against the on-disk content. Reverts the prompt file and
    returns False on any violation. Returns True when the gate passes or
    when inputs cannot be resolved (permissive on missing, mirroring the
    churn gate — the churn gate is still running alongside as a
    magnitude-based belt-and-suspenders).

    Invariants (motivated by PR gltanaka/pdd#1187):
      1. `<include>` / `<include-many>` tag count must not decrease.
      2. Every `<pdd.NAME>` open tag in the original must still appear
         verbatim (prefix included) in the current content.
      3. If the original has `%`-prefixed section markers, the current
         content must retain at least `max(1, ceil(original_count / 2))`.
      4. Every fenced code block in the original must appear verbatim
         (byte-identical) somewhere in the current content.

    Individual invariants can be disabled via the comma-separated env var
    `PDD_HEAL_INVARIANTS_SKIP` — valid names are `include`, `pdd_tags`,
    `percent_markers`, `fenced_blocks`. Motivation: invariant #4 is the
    strictest; legitimate example-code refactors inside a fenced block
    need an escape hatch without a code change here.
    """
    if not drift.prompt_path:
        return True

    original = _git_show_prompt_at_head(drift.prompt_path)
    if original is None:
        return True

    try:
        current = Path(drift.prompt_path).read_text()
    except Exception:
        return True

    skipped = _get_skipped_invariants()
    violations: List[str] = []

    if "include" not in skipped:
        original_include_count = len(_INCLUDE_TAG_RE.findall(original))
        current_include_count = len(_INCLUDE_TAG_RE.findall(current))
        if current_include_count < original_include_count:
            violations.append(
                f"<include>/<include-many> count dropped from "
                f"{original_include_count} to {current_include_count}"
            )

    if "pdd_tags" not in skipped:
        original_pdd_tags = set(_PDD_OPEN_TAG_RE.findall(original))
        missing_pdd_tags = sorted(tag for tag in original_pdd_tags if tag not in current)
        if missing_pdd_tags:
            violations.append(
                "missing <pdd.*> tags (prefix stripped or tag deleted): "
                + ", ".join(missing_pdd_tags)
            )

    if "percent_markers" not in skipped:
        original_percent_lines = _PERCENT_MARKER_RE.findall(original)
        current_percent_count = len(_PERCENT_MARKER_RE.findall(current))
        if original_percent_lines:
            required = max(1, math.ceil(len(original_percent_lines) / 2))
            if current_percent_count < required:
                violations.append(
                    f"% section markers dropped below threshold "
                    f"({current_percent_count} < {required}, "
                    f"original had {len(original_percent_lines)})"
                )

    if "fenced_blocks" not in skipped:
        original_blocks = _FENCED_BLOCK_RE.findall(original)
        missing_blocks = [b for b in original_blocks if b not in current]
        if missing_blocks:
            previews = [b[:80].replace("\n", " ") + "..." for b in missing_blocks]
            violations.append(
                "missing fenced code blocks: " + " | ".join(previews)
            )

    if not violations:
        return True

    console.print(
        f"[red]✗ Structural invariants failed for {drift.basename}:[/red]"
    )
    for v in violations:
        console.print(f"[red]  - {v}[/red]")
    console.print(
        f"[red]  Reverting {drift.prompt_path} — see PR gltanaka/pdd#1187.[/red]"
    )
    _revert_prompt_file(drift)
    return False


def _revert_prompt_file(drift: DriftInfo) -> None:
    """Restore a prompt file to HEAD after a failed heal attempt.

    Raises:
        PromptRevertError: If the prompt path is unavailable, git checkout fails,
            or the prompt still appears modified afterwards.
    """
    if not drift.prompt_path:
        msg = (
            f"Cannot safely revert {drift.basename}: prompt_path is unavailable. "
            "Blocking commit phase to avoid publishing a partial heal."
        )
        console.print(f"[red]✗ {msg}[/red]")
        raise PromptRevertError(msg)
    try:
        rel_prompt_path = _git_repo_relative_path(drift.prompt_path)
        if rel_prompt_path is None:
            msg = (
                f"Cannot safely revert {drift.prompt_path}: could not resolve a "
                "repo-relative git path. Blocking commit phase to avoid "
                "publishing a partial heal."
            )
            console.print(f"[red]✗ {msg}[/red]")
            raise PromptRevertError(msg)

        restore_result = subprocess.run(
            ["git", "checkout", "HEAD", "--", rel_prompt_path],
            check=False,
            capture_output=True,
            text=True,
            timeout=30,
        )
        if restore_result.returncode != 0:
            stderr = (restore_result.stderr or "").strip()
            msg = (
                f"Failed to revert {drift.prompt_path} after heal failure"
                + (f": {stderr}" if stderr else ".")
            )
            console.print(f"[red]✗ {msg}[/red]")
            raise PromptRevertError(msg)

        status_result = subprocess.run(
            ["git", "status", "--porcelain", "--", rel_prompt_path],
            check=False,
            capture_output=True,
            text=True,
            timeout=30,
        )
        if status_result.returncode != 0 or (status_result.stdout or "").strip():
            stderr = (status_result.stderr or "").strip()
            msg = (
                f"Prompt {drift.prompt_path} still appears dirty after revert"
                + (f": {stderr}" if stderr else ".")
            )
            console.print(f"[red]✗ {msg}[/red]")
            raise PromptRevertError(msg)
    except Exception as e:
        if isinstance(e, PromptRevertError):
            raise
        msg = f"Could not revert {drift.prompt_path}: {e}"
        console.print(f"[red]✗ {msg}[/red]")
        raise PromptRevertError(msg) from e


def heal_module(drift: DriftInfo, env: Dict[str, str]) -> Optional[bool]:
    """Heal a single drifted module by running the appropriate pdd command.

    For 'update' drift (code changed, prompt stale), runs pdd update first
    to sync the prompt from code, then pdd sync to regenerate the example
    from the updated prompt — all in one pass.

    Args:
        drift: DriftInfo describing the drift to heal.
        env: Environment variables dict for the subprocess.

    Returns:
        True if healing succeeded, False if it failed, or None if it was
        intentionally skipped by CI policy.
    """
    if drift.operation == "update":
        # Step 1: Update the prompt from code
        if not drift.code_path:
            console.print(
                f"[red]✗ Refusing to run repo-wide `pdd update` for {drift.basename}: "
                "code_path could not be resolved.[/red]"
            )
            return False

        update_cmd = ["pdd", "update", drift.code_path]

        if not _run_pdd_command(update_cmd, env, f"Healing {drift.basename} (update)"):
            return False

        # Change-magnitude gate: refuse prompt rewrites that are wildly
        # out of proportion to the originating code change. When tripped,
        # the prompt file is reverted and the module is treated as
        # unhealed so commit_and_push does not publish a destructive
        # rewrite.
        if not _enforce_prompt_churn_gate(drift):
            return False

        # Structural-invariant gate: path-agnostic post-heal check that
        # the rewrite still contains the <include> preamble, <pdd.*>
        # namespaced tags, % section markers, and fenced code blocks
        # from the pre-heal version. Catches destructive rewrites that
        # slip under the churn-ratio cap.
        if not _enforce_structural_invariants(drift):
            return False

        # Step 2: Sync example from the now-updated prompt so everything is
        # consistent in a single CI pass (no second cycle needed).
        skip_reason = _get_heal_sync_skip_reason(drift.basename)
        if skip_reason:
            console.print(
                f"[yellow]⚠ Skipping follow-up sync for {drift.basename}: "
                f"{skip_reason}. Example regeneration is left for a manual "
                "or dedicated follow-up run.[/yellow]"
            )
            return True
        sync_cmd = ["pdd", "sync", drift.basename]
        if not _run_pdd_command(sync_cmd, env, f"Syncing {drift.basename} (example)"):
            # Update succeeded but sync failed. Revert the prompt update so
            # commit_and_push() cannot stage and publish a half-healed module.
            console.print(
                f"[red]✗ Follow-up example sync failed for {drift.basename}. "
                "Reverting prompt update and marking the module failed.[/red]"
            )
            _revert_prompt_file(drift)
            return False
        return True

    elif drift.operation == "example":
        skip_reason = _get_heal_sync_skip_reason(drift.basename)
        if skip_reason:
            console.print(
                f"[yellow]⚠ Skipping auto-heal sync for {drift.basename}: "
                f"{skip_reason}. This module can be synced in a separate "
                "follow-up run without blocking the PR auto-heal build.[/yellow]"
            )
            return None
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
        unsafe_to_commit = False

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

            revert_failed = False
            try:
                success = heal_module(drift, env)
            except PromptRevertError as e:
                console.print(
                    "[red]✗ Prompt revert failed; blocking commit phase to avoid "
                    "publishing partial heal changes.[/red]"
                )
                unsafe_to_commit = True
                revert_failed = True
                success = False

            # Parse cost from this operation
            operation_cost = _parse_cost_from_csv(cost_csv_path)
            cumulative_cost += operation_cost

            if operation_cost > 0:
                console.print(
                    f"  Cost: ${operation_cost:.4f} "
                    f"(cumulative: ${cumulative_cost:.4f})"
                )

            if success is None:
                skipped_modules.append(drift.basename)
            elif success:
                healed_modules.append(drift.basename)
            else:
                if not revert_failed or drift.basename not in failed_modules:
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
    if unsafe_to_commit:
        console.print(
            "\n[red]✗ Skipping commit phase because a failed heal could not be "
            "safely reverted.[/red]"
        )
    elif healed_modules:
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
