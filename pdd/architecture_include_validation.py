"""
Cross-validate architecture.json dependency entries against <include> tags in prompts.

Phase 5: surface drift between declarative architecture dependencies and the module
prompts the LLM actually pulls in via <include>.
"""
from __future__ import annotations

import json
from pathlib import Path
from typing import Any, Dict, FrozenSet, List

from .sync_order import extract_includes_from_file, extract_module_from_include

# Top-level directories in the PDD repo that ship sample architecture (not app code).
_BUNDLED_SAMPLE_TOPLEVEL_DIRS: FrozenSet[str] = frozenset(
    {"examples", "example_project", "example_workspace", "staging"}
)


def _arch_path_under_skipped_sample_tree(
    arch_path: Path,
    project_root: Path,
    skip_roots: FrozenSet[str],
) -> bool:
    if not skip_roots:
        return False
    try:
        rel = arch_path.resolve().relative_to(project_root.resolve())
    except ValueError:
        return False
    return len(rel.parts) >= 2 and rel.parts[0] in skip_roots


def collect_architecture_include_validation_warnings(
    project_root: Path,
    *,
    skip_bundled_sample_arch: bool = True,
) -> List[str]:
    """
    Run cross-validation for every ``architecture.json`` under ``project_root``.

    Each file is validated with its **parent directory** as the project root for
    resolving ``prompts/…`` paths, so nested packages (e.g. ``services/api/``) work.

    When ``skip_bundled_sample_arch`` is true (default), skips trees like
    ``examples/`` used in the PDD repository so routine sync stays focused on app code.
    """
    from .architecture_registry import find_architecture_for_project

    root = project_root.resolve()
    skip = _BUNDLED_SAMPLE_TOPLEVEL_DIRS if skip_bundled_sample_arch else frozenset()
    warnings: List[str] = []
    for arch_path in find_architecture_for_project(project_root):
        if _arch_path_under_skipped_sample_tree(arch_path, root, skip):
            continue
        try:
            with open(arch_path, "r", encoding="utf-8") as f:
                data = json.load(f)
        except (OSError, json.JSONDecodeError):
            continue
        if not isinstance(data, list) or not data:
            continue
        base = arch_path.parent
        for w in cross_validate_architecture_with_prompt_includes(data, base):
            warnings.append(f"{arch_path}: {w}")
    return warnings


def print_architecture_include_validation_warnings(*, quiet: bool, verbose: bool = False) -> None:
    """Print yellow warnings for the current project only when ``--verbose`` (and not ``--quiet``)."""
    if quiet or not verbose:
        return
    from rich import print as rprint

    from .architecture_registry import find_project_root

    for w in collect_architecture_include_validation_warnings(find_project_root()):
        rprint(f"[yellow]Warning: {w}[/yellow]")


def _resolve_architecture_prompt_path(filename: str, project_root: Path) -> Path:
    """Resolve architecture ``filename`` to an on-disk path under the project."""
    rel = filename.replace("\\", "/").lstrip("/")
    if rel.startswith("prompts/"):
        return (project_root / rel).resolve()
    return (project_root / "prompts" / rel).resolve()


def resolve_architecture_prompt_path(filename: str, project_root: Path) -> Path:
    """Public API for resolving an architecture ``filename`` to an on-disk path."""
    return _resolve_architecture_prompt_path(filename, project_root)


def cross_validate_architecture_with_prompt_includes(
    arch_data: List[Dict[str, Any]],
    project_root: Path,
) -> List[str]:
    """
    Compare each architecture entry's ``dependencies`` (as module basenames) with
    module targets of ``<include>`` tags in the corresponding prompt file.

    Non-module includes (docs, preambles, etc.) are ignored via
    ``extract_module_from_include``.

    Returns:
        Human-readable warning strings (empty if no mismatches / nothing to check).
    """
    warnings: List[str] = []

    filename_to_basename: Dict[str, str] = {}
    for entry in arch_data:
        fn = entry.get("filename") or ""
        if not fn:
            continue
        b = extract_module_from_include(fn)
        if b:
            filename_to_basename[fn] = b

    for entry in arch_data:
        fn = entry.get("filename") or ""
        if not fn:
            continue
        mod_base = filename_to_basename.get(fn)
        if not mod_base:
            continue

        prompt_path = _resolve_architecture_prompt_path(fn, project_root)
        if not prompt_path.is_file():
            warnings.append(
                f"Cross-validation skipped for architecture entry {fn!r}: "
                f"prompt file not found at {prompt_path}"
            )
            continue

        includes = extract_includes_from_file(prompt_path)
        include_modules: set[str] = set()
        include_proof: Dict[str, str] = {}
        for inc in includes:
            m = extract_module_from_include(inc)
            if m and m != mod_base:
                include_modules.add(m)
                include_proof.setdefault(m, inc)

        arch_modules: set[str] = set()
        for dep_fn in entry.get("dependencies", []):
            db = filename_to_basename.get(dep_fn)
            if db and db != mod_base:
                arch_modules.add(db)

        for d in sorted(arch_modules - include_modules):
            dep_fn_proof = next(
                (
                    df
                    for df in entry.get("dependencies", [])
                    if filename_to_basename.get(df) == d
                ),
                None,
            )
            extra = f" ({dep_fn_proof!r})" if dep_fn_proof else ""
            warnings.append(
                f"architecture.json / <include> mismatch: {fn!r} declares dependency on module "
                f"{d!r}{extra} but the prompt has no <include> of that module's prompt"
            )

        for i in sorted(include_modules - arch_modules):
            inc_s = include_proof.get(i, "")
            warnings.append(
                f"architecture.json / <include> mismatch: {fn!r} <include>s module {i!r} "
                f"({inc_s!r}) but architecture.json dependencies do not list that module"
            )

    return warnings
