from __future__ import annotations

import logging
import os
from collections import deque
from pathlib import Path
from typing import Deque, Dict, List, Optional, Set, Tuple

from rich.console import Console
from rich.markdown import Markdown

from .agentic_common import (
    DEFAULT_MAX_RETRIES,
    get_available_agents,
    run_agentic_task,
    _revert_out_of_scope_changes,
)
from .load_prompt_template import load_prompt_template

# Optional dependency: sync_order.extract_includes_from_file is the single
# include parser used by PDD preprocessing/fingerprinting. Falling back to a
# no-op set when sync_order can't be imported keeps the scope guard from
# crashing in degraded environments (e.g. partial installs during tests).
try:
    from .sync_order import extract_includes_from_file
except ImportError:  # pragma: no cover - defensive
    def extract_includes_from_file(file_path: Path) -> Set[str]:  # type: ignore[misc]
        return set()


logger = logging.getLogger(__name__)

# Module-level project root. Exposed as a module attribute so callers (and
# tests) can patch ``pdd.agentic_update.PROJECT_ROOT`` to point at a sandbox
# instead of the real repository.
PROJECT_ROOT: Path = Path.cwd()

console = Console()


def _discover_test_files(
    code_path: Path,
    tests_dir: Optional[Path] = None,
) -> List[Path]:
    """Auto-discover test files for the given code file.

    Search order (Requirement 5 in the spec):
        1. ``tests_dir`` (if provided via config / .pddrc).
        2. ``tests/`` relative to the code file.
        3. The same directory as the code file.
        4. Sibling ``../tests/`` directory.
        5. ``PROJECT_ROOT / "tests"``.
    """
    stem = code_path.stem
    suffix = code_path.suffix
    pattern = f"test_{stem}*{suffix}"

    search_dirs: List[Path] = []
    if tests_dir is not None and tests_dir.exists():
        search_dirs.append(tests_dir)

    rel_tests = code_path.parent / "tests"
    if rel_tests.exists():
        search_dirs.append(rel_tests)

    search_dirs.append(code_path.parent)

    sibling_tests = code_path.parent.parent / "tests"
    if sibling_tests.exists() and sibling_tests not in search_dirs:
        search_dirs.append(sibling_tests)

    root_tests = PROJECT_ROOT / "tests"
    if root_tests.exists() and root_tests not in search_dirs:
        search_dirs.append(root_tests)

    found: List[Path] = []
    seen: Set[Path] = set()
    for d in search_dirs:
        if not d.is_dir():
            continue
        for p in sorted(d.glob(pattern)):
            if p.is_file():
                resolved = p.resolve()
                if resolved not in seen:
                    seen.add(resolved)
                    found.append(p)
    return found


def _compute_include_allowlist(
    prompt_path: Path,
) -> Set[Path]:
    """Cycle-safe BFS over <include> references from a prompt.

    Reuses ``pdd.sync_order.extract_includes_from_file`` as the single include
    parser so this module cannot disagree with PDD preprocessing/fingerprinting
    on what counts as an include. Body-form ``<include path="X">Y</include>``
    resolves to ``X`` (attribute wins), matching the preprocessor.

    Traversal is recursive (no depth cap) to mirror PDD preprocessing, which
    expands nested includes until convergence. The ``visited`` set prevents
    infinite loops on cyclic include graphs.

    Resolution order for each raw include string:
        1. ``PROJECT_ROOT / include_str``
        2. ``current_file.parent / include_str``

    Includes that do not resolve to an existing file under ``PROJECT_ROOT``
    are silently skipped. The helper never raises on missing files or
    unreadable includes — it logs a debug message and continues.
    """
    project_root_resolved = PROJECT_ROOT.resolve()
    prompt_resolved = prompt_path.resolve()

    allowed: Set[Path] = set()
    visited: Set[Path] = set()
    queue: Deque[Path] = deque()
    queue.append(prompt_resolved)

    while queue:
        current_file = queue.popleft()

        if current_file in visited:
            continue
        visited.add(current_file)

        try:
            includes = extract_includes_from_file(current_file)
        except Exception as exc:  # pragma: no cover - defensive
            logger.debug("extract_includes_from_file failed for %s: %s",
                         current_file, exc)
            continue

        for inc_str in includes:
            if not inc_str:
                continue
            candidates = [
                (project_root_resolved / inc_str),
                (current_file.parent / inc_str),
            ]
            resolved_path: Optional[Path] = None
            for candidate in candidates:
                try:
                    candidate_resolved = candidate.resolve()
                except OSError as exc:  # pragma: no cover - defensive
                    logger.debug("Could not resolve %s: %s", candidate, exc)
                    continue
                if not candidate_resolved.exists():
                    continue
                try:
                    candidate_resolved.relative_to(project_root_resolved)
                except ValueError:
                    # Outside PROJECT_ROOT — skip.
                    continue
                resolved_path = candidate_resolved
                break

            if resolved_path is None:
                logger.debug("Include %r not resolvable under %s",
                             inc_str, project_root_resolved)
                continue

            if resolved_path not in allowed:
                allowed.add(resolved_path)
            if resolved_path not in visited:
                queue.append(resolved_path)

    return allowed


def _snapshot_mtimes(
    root: Path,
    extra_paths: Optional[List[Path]] = None,
) -> Dict[Path, float]:
    """Snapshot mtimes for every file under ``root`` (skipping .git).

    Additional paths in ``extra_paths`` are also recorded, even if they lie
    outside ``root`` — this lets us track the prompt/code/test files when
    the caller passes paths outside ``PROJECT_ROOT`` (common in tests).
    """
    mtimes: Dict[Path, float] = {}
    if root.exists():
        for p in root.rglob("*"):
            try:
                rel = p.relative_to(root)
            except ValueError:
                continue
            if rel.parts and rel.parts[0] == ".git":
                continue
            if p.is_file():
                try:
                    mtimes[p.resolve()] = p.stat().st_mtime
                except OSError:
                    pass
    if extra_paths:
        for ep in extra_paths:
            try:
                resolved = ep.resolve()
            except OSError:
                continue
            if resolved.is_file():
                try:
                    mtimes[resolved] = resolved.stat().st_mtime
                except OSError:
                    pass
            # Also scan one level for sibling test files that may appear.
            parent = resolved.parent
            if parent.is_dir():
                for sib in parent.iterdir():
                    if sib.is_file():
                        try:
                            mtimes.setdefault(sib.resolve(), sib.stat().st_mtime)
                        except OSError:
                            pass
    return mtimes


def _detect_changed_files(
    root: Path,
    old_mtimes: Dict[Path, float],
    extra_paths: Optional[List[Path]] = None,
) -> List[Path]:
    """Detect created, modified, or deleted files since ``old_mtimes``."""
    new_mtimes = _snapshot_mtimes(root, extra_paths=extra_paths)
    changed: Set[Path] = set()

    for p, old_t in old_mtimes.items():
        if p not in new_mtimes:
            # File was deleted.
            changed.add(p)
        elif new_mtimes[p] != old_t:
            changed.add(p)

    for p in new_mtimes:
        if p not in old_mtimes:
            changed.add(p)

    return sorted(changed)


def run_agentic_update(
    prompt_file: str,
    code_file: str,
    test_files: Optional[List[Path]] = None,
    *,
    tests_dir: Optional[Path] = None,
    verbose: bool = False,
    quiet: bool = False,
) -> Tuple[bool, str, float, str, List[str]]:
    """Coordinate an agentic prompt update via available CLI agents.

    Args:
        prompt_file: Path to the prompt file (the spec / source of truth).
        code_file: Path to the modified code file.
        test_files: Optional explicit list of test file paths. When ``None``,
            tests are auto-discovered. An empty list disables discovery.
        tests_dir: Optional config-supplied directory to search for tests.
        verbose: Forwarded to the agent runner.
        quiet: When True, no console output is produced.

    Returns:
        ``(success, message, cost, model_used, changed_files)``. ``success``
        is True only when the prompt file itself was modified during the run.
    """
    prompt_path = Path(prompt_file).resolve()
    code_path = Path(code_file).resolve()

    # 1. File existence checks.
    if not prompt_path.exists():
        msg = f"Prompt file not found: {prompt_file}"
        if not quiet:
            console.print(f"[red]{msg}[/red]")
        return False, msg, 0.0, "", []

    if not code_path.exists():
        msg = f"Code file not found: {code_file}"
        if not quiet:
            console.print(f"[red]{msg}[/red]")
        return False, msg, 0.0, "", []

    # 2. Agent availability check (Requirement 3).
    try:
        agents = get_available_agents()
    except Exception as exc:
        msg = f"Failed to check agent availability: {exc}"
        if not quiet:
            console.print(f"[red]{msg}[/red]")
        return False, msg, 0.0, "", []

    if not agents:
        # Spec: exact message "No agentic CLI available".
        return False, "No agentic CLI available", 0.0, "", []

    # 3. Test file selection (Requirement 4).
    selected_tests: List[Path] = []
    if test_files is not None:
        missing: List[Path] = [tf for tf in test_files if not tf.exists()]
        if missing:
            missing_str = ", ".join(str(m) for m in missing)
            msg = f"Test file(s) not found: {missing_str}"
            if not quiet:
                console.print(f"[red]{msg}[/red]")
            return False, msg, 0.0, "", []
        selected_tests = [tf.resolve() for tf in test_files]
    else:
        selected_tests = [
            t.resolve() for t in _discover_test_files(code_path, tests_dir)
        ]

    # 4. Template loading (Requirement 6).
    try:
        template = load_prompt_template("agentic_update_LLM")
    except Exception as exc:
        msg = f"Error while loading prompt template: {exc}"
        if not quiet:
            console.print(f"[red]{msg}[/red]")
        return False, msg, 0.0, "", []

    if not template:
        msg = "Prompt template 'agentic_update_LLM' could not be loaded"
        if not quiet:
            console.print(f"[red]{msg}[/red]")
        return False, msg, 0.0, "", []

    # Format the template with the prompt/code/test paths.
    if selected_tests:
        test_paths_str = "\n".join(f"- {p}" for p in selected_tests)
    else:
        test_paths_str = "No tests were found."

    try:
        prompt_text = template.format(
            prompt_path=str(prompt_path),
            code_path=str(code_path),
            test_paths=test_paths_str,
        )
    except Exception as exc:
        msg = f"Error formatting prompt template: {exc}"
        if not quiet:
            console.print(f"[red]{msg}[/red]")
        return False, msg, 0.0, "", []

    # 5. Snapshot the project tree before the agent runs. Always include the
    # explicit prompt/code/test paths so callers passing files outside
    # ``PROJECT_ROOT`` (e.g. tests using ``tmp_path``) still see changes.
    extra_tracked: List[Path] = [prompt_path, code_path] + list(selected_tests)
    old_mtimes = _snapshot_mtimes(PROJECT_ROOT, extra_paths=extra_tracked)

    if not quiet:
        console.print(
            f"[blue]Starting agentic update for {prompt_path.name}...[/blue]"
        )

    # 6. Execute the agentic task (Requirement 7).
    try:
        agent_success, agent_message, cost, model = run_agentic_task(
            prompt_text,
            PROJECT_ROOT,
            verbose=verbose,
            quiet=quiet,
            label="agentic_update",
            max_retries=DEFAULT_MAX_RETRIES,
        )
    except TypeError:
        # Test fixtures may patch run_agentic_task with a simpler signature
        # (e.g. *args, **kwargs); fall back to a minimal positional call so
        # mocks that ignore cwd still work.
        try:
            agent_success, agent_message, cost, model = run_agentic_task(
                prompt_text,
                max_retries=DEFAULT_MAX_RETRIES,
                verbose=verbose,
            )
        except Exception as exc:
            msg = f"Agentic task failed with an exception: {exc}"
            if not quiet:
                console.print(f"[red]{msg}[/red]")
            return False, msg, 0.0, "", []
    except Exception as exc:
        msg = f"Agentic task failed with an exception: {exc}"
        if not quiet:
            console.print(f"[red]{msg}[/red]")
        return False, msg, 0.0, "", []

    # 7. Scope guard (Requirement 10): revert any out-of-scope mutations
    # before observing the changed-file set, so we don't report files that
    # are about to be undone.
    allowed_paths: Set[Path] = {prompt_path, code_path}
    allowed_paths.update(p.resolve() for p in selected_tests)
    allowed_paths.update(_compute_include_allowlist(prompt_path))

    try:
        _revert_out_of_scope_changes(PROJECT_ROOT, allowed_paths)
    except Exception as exc:  # pragma: no cover - defensive
        logger.debug("Scope guard raised: %s", exc)

    # 8. Re-discover tests post-run so newly-created test files are visible
    # to the caller (Requirement 8).
    if test_files is None:
        post_run_tests = [
            t.resolve() for t in _discover_test_files(code_path, tests_dir)
        ]
    else:
        post_run_tests = [tf.resolve() for tf in test_files if tf.exists()]

    # 9. Detect changed files via mtime comparison.
    post_extras: List[Path] = (
        [prompt_path, code_path] + list(selected_tests) + list(post_run_tests)
    )
    changed_paths = _detect_changed_files(
        PROJECT_ROOT, old_mtimes, extra_paths=post_extras
    )
    changed_set = {p for p in changed_paths}

    # Make sure newly discovered tests are visible even if rglob missed them.
    for tp in post_run_tests:
        if tp.exists() and tp not in old_mtimes:
            changed_set.add(tp)

    # 10. Success criterion (Requirement 9): the prompt file itself must
    # have been modified.
    try:
        new_prompt_mtime = prompt_path.stat().st_mtime
    except OSError:
        new_prompt_mtime = None
    old_prompt_mtime = old_mtimes.get(prompt_path)

    prompt_modified = (
        new_prompt_mtime is not None
        and (old_prompt_mtime is None or new_prompt_mtime != old_prompt_mtime)
    )

    changed_str_list = sorted(str(p) for p in changed_set)

    # Render the agent's output (Markdown) when not quiet.
    if not quiet and agent_message:
        try:
            console.print(Markdown(agent_message))
        except Exception:  # pragma: no cover - defensive
            console.print(agent_message)

    if prompt_modified:
        if agent_success:
            msg = f"Prompt file updated successfully: {prompt_path.name}"
        else:
            msg = (
                "Prompt file updated successfully, although the underlying "
                f"agent reported failure: {prompt_path.name}. "
                "Underlying agent reported failure."
            )
        return True, msg, cost, model, changed_str_list

    msg = (
        f"Agent ran but did not modify the prompt file: {prompt_path.name}"
    )
    return False, msg, cost, model, changed_str_list
