"""
sync_determine_operation.py
~~~~~~~~~~~~~~~~~~~~~~~~~

Core decision-making logic for the `pdd sync` command.
Implements fingerprint-based state analysis and deterministic operation selection.
"""

import os
import re
import sys
import glob
import json
import hashlib
import subprocess
import fnmatch
import unicodedata
from functools import lru_cache
from pathlib import Path, PurePosixPath, PureWindowsPath
from dataclasses import dataclass, field
from typing import Dict, List, Optional, Any, Tuple
from datetime import datetime
import psutil

# Platform-specific imports for file locking
try:
    import fcntl
    HAS_FCNTL = True
except ImportError:
    HAS_FCNTL = False

try:
    import msvcrt
    HAS_MSVCRT = True
except ImportError:
    HAS_MSVCRT = False

# Import PDD internal modules
from pdd.construct_paths import (
    _detect_context,
    _detect_context_from_basename,
    _extract_prefix_from_prompts_dir,
    _find_pddrc_file,
    _get_relative_basename,
    _load_pddrc_config,
    construct_paths,
)
from pdd.load_prompt_template import load_prompt_template
from pdd.llm_invoke import llm_invoke
from pdd.get_language import get_language
from pdd.template_expander import expand_template
from pdd.architecture_registry import extract_modules
from pdd.sync_order import extract_module_from_include

# Constants - Use functions for dynamic path resolution
def get_pdd_dir():
    """Get the .pdd directory relative to current working directory."""
    return Path.cwd() / '.pdd'

def get_meta_dir(project_root=None, paths=None):
    """Get the metadata directory.

    Resolution order (Issue #1211):
      1. Explicit `project_root` argument
      2. .pddrc reachable upward from any path in `paths`
         (handles a subproject .pddrc that lives BELOW run CWD)
      3. .pddrc reachable upward from CWD
      4. Run CWD (legacy behavior)
    """
    if project_root is not None:
        return Path(project_root) / '.pdd' / 'meta'
    try:
        from .operation_log import _resolve_meta_dir
    except ImportError:  # direct (non-package) import path
        from operation_log import _resolve_meta_dir  # type: ignore
    return _resolve_meta_dir(project_root=None, paths=paths)

def get_locks_dir():
    """Get the locks directory."""
    return get_pdd_dir() / 'locks'

# For backward compatibility
PDD_DIR = get_pdd_dir()
META_DIR = get_meta_dir()
LOCKS_DIR = get_locks_dir()

# Export constants for other modules
__all__ = ['PDD_DIR', 'META_DIR', 'LOCKS_DIR', 'Fingerprint', 'RunReport', 'SyncDecision',
           'sync_determine_operation', 'analyze_conflict_with_llm', 'read_run_report', 'get_pdd_file_paths',
           '_check_example_success_history', 'AmbiguousModuleError', 'UnsafePromptPathError']


class AmbiguousModuleError(ValueError):
    """Raised when a bare module basename maps to more than one architecture module.

    Issue #1677: short basenames such as ``page`` (common in Next.js projects where
    many files are named ``page.tsx``/``layout.tsx``) are not a stable module
    identity. When such a name matches multiple ``architecture.json`` entries that
    resolve to *different* output files, ``pdd sync`` must fail before generating
    files instead of silently picking one (first-match-wins) or falling back to a
    ``.pddrc`` default path like ``frontend/src/page.tsx``.

    Subclasses :class:`ValueError` so that existing best-effort callers of
    :func:`get_pdd_file_paths` (operation logging, drift heal, evidence/checkup
    gates) degrade gracefully via their broad ``except`` clauses, while sync
    *generation* paths explicitly re-raise it to fail fast.
    """

    def __init__(self, basename: str, language: str, choices: List[str]):
        self.basename = basename
        self.language = language
        self.choices = list(choices)
        choice_lines = "\n".join(f"  - {c}" for c in self.choices)
        super().__init__(
            f"Ambiguous module '{basename}' for language {language}: it maps to "
            f"{len(self.choices)} different files in architecture.json:\n{choice_lines}\n"
            f"Re-run with a path-qualified module name (e.g. the prompt's directory "
            f"path, like 'app/login/{basename}') so PDD writes to the intended file."
        )


class UnsafePromptPathError(AmbiguousModuleError):
    """Raised when a prompt candidate resolves outside its configured root.

    This subclasses the existing hard path-resolution error so every sync entry
    point that already propagates :class:`AmbiguousModuleError` also fails closed
    before generation can write through an escaping symlink.
    """

    def __init__(self, prompt_path: Path, prompts_root: Path):
        self.prompt_path = prompt_path
        self.prompts_root = prompts_root
        ValueError.__init__(
            self,
            f"Unsafe prompt path '{prompt_path}' resolves outside prompts root "
            f"'{prompts_root}'",
        )


class MalformedArchitectureError(AmbiguousModuleError):
    """Raised when a DISCOVERED architecture.json exists but cannot be read/parsed.

    Subclasses the hard path-resolution error so every sync entry point that already
    propagates :class:`AmbiguousModuleError` fails closed rather than silently resolving
    at convention fallback paths — which can mis-target the authoritative registered
    code file instead of the one the (present but broken) registry intended.
    """

    def __init__(self, architecture_path: Path, reason: object):
        self.architecture_path = architecture_path
        ValueError.__init__(
            self,
            f"architecture.json at '{architecture_path}' is present but could not be "
            f"read/parsed ({reason}); fix or remove it — refusing to resolve at "
            f"convention fallback paths.",
        )


class UnsafeOutputPathError(AmbiguousModuleError):
    """Raised when a resolved code/example/test output escapes the project root.

    Architecture code filepaths are already contained by
    :func:`_contained_architecture_code_path` (R7), but the *destination* of an
    output can also come from ``.pddrc`` configuration — ``generate_output_path``,
    ``example_output_path``/``test_output_path``, and ``outputs.*.path`` templates.
    A configured value with parent traversal, an escaping symlink, or an absolute
    path pointing away from the project would otherwise let sync (or even dry-run
    path discovery) create/write files outside the project tree. Subclassing the
    hard path-resolution error means every sync entry point that already fails
    closed on :class:`AmbiguousModuleError` also refuses an out-of-tree output,
    while best-effort callers (logging, drift heal, checkup) degrade gracefully.
    """

    def __init__(self, output_path: object, project_root: object, artifact: str):
        self.output_path = output_path
        self.project_root = project_root
        self.artifact = artifact
        ValueError.__init__(
            self,
            f"Unsafe {artifact} output path '{output_path}' resolves outside "
            f"project root '{project_root}'",
        )


def _safe_basename(basename: str) -> str:
    """Sanitize basename for use in metadata filenames.

    Replaces '/' with '_' to prevent path interpretation when the basename
    contains subdirectory components (e.g., 'core/cloud' -> 'core_cloud').
    """
    return basename.replace('/', '_')


def _safe_lock_component(value: Any) -> str:
    """Collapse a lock-name component to a portable, separator-free token.

    Lock filenames are built from the caller basename and language BEFORE
    :func:`get_pdd_file_paths` validates those inputs (the lock is acquired
    first). A traversal- or separator-bearing ``language`` (e.g.
    ``/../../../tmp/victim``) would otherwise interpolate into the lock path and
    let ``SyncLock`` mkdir/touch/unlink an out-of-tree ``.lock`` file. Replacing
    every character outside ``[A-Za-z0-9._-]`` with ``_`` yields a flat token
    that cannot contain a path separator, ``:``, or drive marker, so the lock
    file is always confined to the locks directory. Valid identifiers
    (``python``, ``core/cloud`` -> ``core_cloud``) are unaffected.
    """
    return re.sub(r"[^A-Za-z0-9._-]", "_", str(value))


def is_test_extend_disabled() -> bool:
    """Return True when coverage-driven ``test_extend`` is opted out via env.

    The ``PDD_DISABLE_TEST_EXTEND`` flag is the PR auto-heal scope guard
    (issue #1403): when set, a Python module whose tests pass but whose
    coverage is below target is accepted as complete instead of escalating
    into ``test_extend``, which would append unrelated generated tests and
    re-bloat a narrowly scoped fix PR. Honored by both the in-process
    detection call and the ``pdd sync`` subprocess that inherits the flag.
    """
    return os.environ.get("PDD_DISABLE_TEST_EXTEND", "").strip().lower() in (
        "1",
        "true",
        "yes",
        "on",
    )


def _extract_name_part(basename: str) -> tuple:
    """Extract directory and name parts from a subdirectory basename.

    For subdirectory basenames like 'core/cloud', separates the directory
    prefix from the actual name so that filename patterns can be applied
    correctly.

    Args:
        basename: The full basename, possibly containing subdirectory path.

    Returns:
        Tuple of (dir_prefix, name_part):
        - 'core/cloud' -> ('core/', 'cloud')
        - 'calculator' -> ('', 'calculator')
    """
    if '/' in basename:
        dir_part, name_part = basename.rsplit('/', 1)
        return dir_part + '/', name_part
    return '', basename


def _leading_overlap(base: List[str], sub: List[str]) -> int:
    """Number of leading ``sub`` components already provided by ``base``.

    The larger of two alignments: ``base``'s TAIL equals ``sub``'s HEAD
    (``src/app`` + ``app/login``) or a shared PREFIX/area (``frontend/src`` +
    ``frontend/app/login``).
    """
    tail_head = 0
    for k in range(min(len(base), len(sub)), 0, -1):
        if base[-k:] == sub[:k]:
            tail_head = k
            break
    common_prefix = 0
    for j in range(min(len(base), len(sub)), 0, -1):
        if base[:j] == sub[:j]:
            common_prefix = j
            break
    return max(tail_head, common_prefix)


def _reanchor_under_basename_subdir(
    path_value: Any, basename: str, project_root: Optional[Path] = None
) -> Path:
    """Re-anchor an output path under a path-qualified basename's subdirectory.

    Issue #1677: only used when a module has no architecture entry (construct_paths
    then collapses a path-qualified basename to its bare leaf). Inserts the basename's
    subdirectory so ``foo/page`` writes to ``src/foo/page.tsx`` rather than
    ``src/page.tsx``, while not duplicating a directory segment the output already
    provides.

    The overlap is measured against the computed path's parent made RELATIVE to the
    project root (or cwd), so it reflects whatever output directory construct_paths
    actually used — honoring env vars, absolute config values and context selection —
    without being fooled by the absolute repo prefix:

    * ``frontend/src`` + ``frontend/app/login`` -> ``frontend/src/app/login`` (shared area)
    * ``src/app`` + ``app/login`` -> ``src/app/login`` (tail/head)
    * repo under ``/x/foo`` with ``src/`` + ``foo`` -> ``/x/foo/src/foo/page`` (the repo
      ``foo`` is in the stripped prefix, not the relative output dir)
    * a subdir construct_paths already preserved (``examples/foo``) collapses to no
      remainder and the path is returned unchanged.
    """
    path_obj = Path(path_value)
    if "/" not in basename:
        return path_obj
    dir_prefix, _ = _extract_name_part(basename)
    # Drop empty, current- and parent-directory segments so a basename can never
    # introduce a path-traversal component (".."/".") into the re-anchored output
    # path (CodeQL: uncontrolled data in path expression). A module's directory is
    # always a plain forward-relative path.
    sub = [
        p
        for p in dir_prefix.replace("\\", "/").split("/")
        if p and p not in (".", "..")
    ]
    if not sub:
        return path_obj

    anchor = project_root or Path.cwd()
    try:
        base_dir_parts = list(path_obj.parent.resolve(strict=False).relative_to(anchor.resolve(strict=False)).parts)
    except (ValueError, OSError):
        base_dir_parts = list(path_obj.parent.parts)

    remaining = sub[_leading_overlap(base_dir_parts, sub):]
    if not remaining:
        return path_obj
    return path_obj.parent.joinpath(*remaining, path_obj.name)


def _find_architecture_json(start_path: Optional[Path] = None) -> Optional[Path]:
    """Find architecture.json by searching upward from start_path.

    Searches for architecture.json in the current directory and parent
    directories, stopping at the filesystem root or when .pddrc is found.

    Args:
        start_path: Starting path for the search. Defaults to cwd.

    Returns:
        Path to architecture.json if found, None otherwise.
    """
    current = start_path or Path.cwd()

    while current != current.parent:
        arch_path = current / "architecture.json"
        if arch_path.exists():
            return arch_path
        # Also check if we've reached a project root (contains .pddrc)
        if (current / ".pddrc").exists():
            # Check one more time in this directory
            if arch_path.exists():
                return arch_path
            break
        current = current.parent

    return None


def _join_prompt_path_from_architecture(
    prompts_root: Path,
    architecture_filename: str,
) -> Optional[Path]:
    """Join an architecture prompt name without duplicating root segments."""
    arch_path = _safe_architecture_prompt_filename(architecture_filename)
    if arch_path is None:
        return None

    arch_parts = arch_path.parts
    root_parts = prompts_root.parts
    max_overlap = min(len(root_parts), len(arch_parts))
    overlap = 0

    for candidate in range(max_overlap, 0, -1):
        if root_parts[-candidate:] == arch_parts[:candidate]:
            overlap = candidate
            break

    return prompts_root.joinpath(*arch_parts[overlap:])


def _resolve_prompt_path_from_architecture(
    prompts_root: Path,
    architecture_filename: str,
    context_prefix: Optional[str] = None,
    basename: Optional[str] = None,
) -> Optional[Path]:
    """Build a prompt path from architecture.json without duplicating subdirectories.

    Issue #1169: If the directly joined path does not exist on disk, search
    recursively under prompts_root for a case-insensitive filename match.
    Handles the common case where architecture.json stores just the filename
    (e.g. "firestore_client_Python.prompt") while the file lives in a nested
    subdirectory (e.g. prompts/src/clients/).

    When a legacy FLAT architecture filename matches the same leaf in more than one
    context subdirectory, ``context_prefix`` (from the resolving ``.pddrc`` context)
    selects the correct context's prompt instead of the shallowest/lexicographic
    first — otherwise the hint returns the wrong context's prompt while code resolves
    under the requested one (a torn cross-context pair).
    """
    safe_filename = _safe_architecture_prompt_filename(architecture_filename)
    if safe_filename is None:
        return None
    joined = _join_prompt_path_from_architecture(prompts_root, architecture_filename)
    if joined is None:
        return None
    relative_parts = _prompt_relative_parts_for_root(prompts_root, safe_filename)
    resolved_joined, contained = _walk_prompt_relative_path(
        prompts_root,
        relative_parts,
    )
    if not contained:
        return None
    if (
        resolved_joined
        and (basename is None or _prompt_candidate_aligns_basename(resolved_joined, basename))
        and (
            not context_prefix
            or _prompt_path_has_context_prefix(resolved_joined, prompts_root, context_prefix)
        )
    ):
        return resolved_joined

    # Recursive search for the filename under prompts_root. Collect all matches
    # and pick the shallowest deterministically to avoid platform-dependent
    # filesystem ordering when multiple nested files share the basename.
    if prompts_root.is_dir():
        target_lower = Path(architecture_filename).name.lower()
        resolved_root = prompts_root.resolve(strict=False)
        matches = []
        unsafe_matches = []
        for candidate in prompts_root.rglob("*.prompt"):
            if not candidate.is_file() or candidate.name.lower() != target_lower:
                continue
            if basename is not None and not _prompt_candidate_aligns_basename(
                candidate, basename
            ):
                continue
            try:
                candidate.resolve(strict=False).relative_to(resolved_root)
            except (OSError, RuntimeError, ValueError):
                unsafe_matches.append(candidate)
                continue
            matches.append(candidate)
        if matches and context_prefix:
            matches = [
                m for m in matches
                if _prompt_path_has_context_prefix(m, prompts_root, context_prefix)
            ]
        if matches:
            matches.sort(key=lambda p: (len(p.parts), str(p)))
            return matches[0]
        if unsafe_matches:
            relevant_unsafe = unsafe_matches
            if context_prefix:
                relevant_unsafe = [
                    candidate for candidate in unsafe_matches
                    if _prompt_path_has_context_prefix(
                        candidate, prompts_root, context_prefix
                    )
                ]
            if relevant_unsafe:
                raise UnsafePromptPathError(relevant_unsafe[0], resolved_root)

    if basename is not None and not _prompt_candidate_aligns_basename(joined, basename):
        return None
    # A context prefix scopes EVERY architecture-hint return, not only the recursive
    # matches: a flat/lexical join that lacks the resolving context's prefix must not
    # be returned (it would pair a wrong-context prompt with the requested context's
    # code). Fall through to the caller's context-anchored construction instead.
    if context_prefix and not _prompt_path_has_context_prefix(
        joined, prompts_root, context_prefix
    ):
        return None
    return joined


def _case_insensitive_path_lookup(candidate: Path) -> Optional[Path]:
    """Return the on-disk path for ``candidate`` with case-insensitive filename matching."""
    if candidate.parent.is_dir():
        target_lower = candidate.name.lower()
        fallback_match = None
        for sibling in candidate.parent.iterdir():
            if not sibling.is_file():
                continue
            if sibling.name == candidate.name:
                return sibling
            if fallback_match is None and sibling.name.lower() == target_lower:
                fallback_match = sibling
        if fallback_match is not None:
            return fallback_match
    if candidate.exists():
        return candidate
    return None


def _find_named_file(parent: Path, filename: str) -> Optional[Path]:
    """Find a filename by scanning a directory instead of joining an input leaf.

    An exact-cased match wins. Otherwise the case-insensitive fallback is chosen by
    a stable ``(name, path)`` sort so a case-fold collision on a case-sensitive
    filesystem (e.g. ``Foo_example.py`` beside ``FOO_example.py``) resolves the same
    way regardless of directory iteration order.
    """
    if not parent.is_dir():
        return None
    target_lower = filename.lower()
    fallback_matches: List[Path] = []
    for child in parent.iterdir():
        if not child.is_file():
            continue
        if child.name == filename:
            return child
        if child.name.lower() == target_lower:
            fallback_matches.append(child)
    if not fallback_matches:
        return None
    return sorted(fallback_matches, key=lambda p: (p.name, str(p)))[0]


def _contains_disallowed_path_text(value: str) -> bool:
    """Return whether text contains controls or Unicode line/format separators."""
    return any(
        unicodedata.category(char) in {"Cc", "Cf", "Cs", "Zl", "Zp"}
        for char in value
    )


def _unsafe_portable_path_component(part: str) -> bool:
    """Return whether one POSIX component is invalid or special on Windows."""
    windows_identity = part.rstrip(" .").split(".", 1)[0].upper()
    reserved_windows_names = {
        "CON", "PRN", "AUX", "NUL", "CONIN$", "CONOUT$", "CLOCK$",
    }
    return (
        any(char in '<>:"\\|?*' for char in part)
        or part.endswith((" ", "."))
        or windows_identity in reserved_windows_names
        or (
            len(windows_identity) == 4
            and windows_identity[:3] in {"COM", "LPT"}
            and windows_identity[3] in "123456789¹²³"
        )
    )


def _safe_architecture_prompt_filename(value: Any) -> Optional[PurePosixPath]:
    """Return one safe repository-relative architecture filename.

    Architecture filenames are metadata, not trusted filesystem paths. Prompt
    discovery must never follow absolute paths, parent traversal, backslashes,
    or empty values supplied by that metadata.
    """
    if not isinstance(value, str):
        return None
    if value != value.strip():
        return None
    if _contains_disallowed_path_text(value):
        return None
    raw = value
    if not raw or "\\" in raw:
        return None
    # Windows drive-qualified metadata (e.g. "D:/x", "D:x") is relative to
    # PurePosixPath but escapes the repository when joined on Windows, where a
    # differing drive yields a drive-relative path outside prompts_root. Reject it.
    if PureWindowsPath(raw).drive:
        return None
    filename = PurePosixPath(raw)
    if (
        not filename.parts
        or filename.as_posix() != raw
        or filename.is_absolute()
        or ".." in filename.parts
    ):
        return None
    if any(_unsafe_portable_path_component(part) for part in filename.parts):
        return None
    return filename


def _safe_prompt_language(value: Any) -> Optional[str]:
    """Return a language safe to interpolate as one prompt filename component."""
    safe = _safe_architecture_prompt_filename(value)
    if (
        safe is None
        or len(safe.parts) != 1
        or any(char.isspace() for char in safe.parts[0])
    ):
        return None
    return safe.parts[0]


@lru_cache(maxsize=512)
def _directory_entry_index(
    directory: str,
    modified_ns: int,
) -> Tuple[Dict[str, Tuple[Path, ...]], Dict[str, Tuple[Path, ...]]]:
    """Index one directory; ``modified_ns`` invalidates add/remove/rename."""
    del modified_ns  # Cache-key only.
    directories: Dict[str, List[Path]] = {}
    files: Dict[str, List[Path]] = {}
    with os.scandir(directory) as entries:
        for entry in entries:
            path = Path(entry.path)
            try:
                if entry.is_dir():
                    directories.setdefault(entry.name.lower(), []).append(path)
                elif entry.is_file():
                    files.setdefault(entry.name.lower(), []).append(path)
            except OSError:
                continue
    def _stable(values: List[Path]) -> Tuple[Path, ...]:
        return tuple(
            sorted(values, key=lambda path: (path.name.casefold(), path.name, str(path)))
        )

    return (
        {key: _stable(value) for key, value in directories.items()},
        {key: _stable(value) for key, value in files.items()},
    )


def _indexed_directory_child(
    parent: Path,
    name: str,
    *,
    directory: bool,
) -> Optional[Path]:
    """Return an exact/case-insensitive child from a bounded cached index."""
    try:
        stat = parent.stat()
        directories, files = _directory_entry_index(
            str(parent),
            stat.st_mtime_ns,
        )
    except (OSError, RuntimeError):
        return None
    matches = (directories if directory else files).get(name.lower(), ())
    if not matches:
        return None
    return next((match for match in matches if match.name == name), matches[0])


def _walk_prompt_relative_path(
    root: Path,
    relative_parts: Tuple[str, ...],
) -> Tuple[Optional[Path], bool]:
    """Find a relative prompt by walking only children of a trusted root.

    No metadata-derived path is passed to a filesystem API. Each directory or
    file used for the next step comes from listing the already-contained parent,
    which both avoids path-injection sinks and avoids recursive tree scans.
    """
    if not relative_parts:
        return None, True
    try:
        resolved_root = root.resolve(strict=False)
    except (OSError, RuntimeError):
        return None, False
    current = root
    for part in relative_parts[:-1]:
        current = _indexed_directory_child(current, part, directory=True)
        if current is None:
            return None, True
        try:
            current.resolve(strict=False).relative_to(resolved_root)
        except (OSError, RuntimeError, ValueError):
            return None, False

    found = _indexed_directory_child(
        current,
        relative_parts[-1],
        directory=False,
    )
    if found is None:
        return None, True
    try:
        found.resolve(strict=False).relative_to(resolved_root)
    except (OSError, RuntimeError, ValueError):
        return None, False
    return found, True


def _prompt_relative_parts_for_root(
    root: Path,
    architecture_filename: PurePosixPath,
) -> Tuple[str, ...]:
    """Strip directory segments already represented by a prompt root."""
    arch_parts = architecture_filename.parts
    root_parts = root.parts
    overlap = 0
    for candidate in range(min(len(root_parts), len(arch_parts)), 0, -1):
        if tuple(part.lower() for part in root_parts[-candidate:]) == tuple(
            part.lower() for part in arch_parts[:candidate]
        ):
            overlap = candidate
            break
    return tuple(arch_parts[overlap:])


def _prompt_path_has_context_prefix(
    candidate: Path,
    prompts_root: Path,
    context_prefix: str,
) -> bool:
    """Return whether a candidate is under an exact context path prefix.

    Context names are path components, not substrings: ``backend`` must match
    ``backend/foo.prompt`` but not ``a-backend/foo.prompt``. Comparing components
    also supports nested prefixes such as ``backend/utils``.
    """
    try:
        relative_parts = candidate.relative_to(prompts_root).parts
    except ValueError:
        return False
    prefix_parts = PurePosixPath(context_prefix.replace("\\", "/")).parts
    if not prefix_parts or len(prefix_parts) > len(relative_parts):
        return False
    return tuple(part.lower() for part in relative_parts[:len(prefix_parts)]) == tuple(
        part.lower() for part in prefix_parts
    )


def _prompt_candidate_aligns_basename(candidate: Path, basename: str) -> bool:
    """Whether a prompt candidate aligns with a path-qualified module basename."""
    basename_parts = PurePosixPath(basename).parts
    if len(basename_parts) <= 1:
        return True
    module_leaf = extract_module_from_include(candidate.name) or candidate.stem
    module_parts = candidate.parent.parts + (module_leaf,)
    return len(basename_parts) <= len(module_parts) and tuple(
        part.lower() for part in module_parts[-len(basename_parts):]
    ) == tuple(part.lower() for part in basename_parts)


def _context_prefix_for_prompts_root(
    configured_prompts_dir: Any,
    pddrc_path: Path,
    prompts_root: Path,
) -> Optional[str]:
    """Return a configured context root relative to the active prompt root.

    Custom roots need filesystem-relative normalization: for an active ``specs``
    root, ``specs/frontend`` scopes candidates by ``frontend``, not by the raw
    ``specs/frontend`` configuration string.
    """
    if not isinstance(configured_prompts_dir, str) or not configured_prompts_dir.strip():
        return None
    configured_path = Path(configured_prompts_dir.strip())
    if not configured_path.is_absolute():
        configured_path = pddrc_path.parent / configured_path
    try:
        relative = configured_path.resolve(strict=False).relative_to(
            prompts_root.resolve(strict=False)
        )
    except (OSError, RuntimeError, ValueError):
        return None
    return relative.as_posix() if relative.parts else None


def _architecture_prompt_roots(
    prompts_root: Path,
    architecture_path: Path,
) -> Tuple[Path, ...]:
    """Return contained roots that can own architecture prompt filenames."""
    project_root = architecture_path.parent.resolve(strict=False)
    candidates: List[Path] = [
        prompts_root.resolve(strict=False),
        project_root / "prompts",
        project_root / "pdd" / "prompts",
    ]

    pddrc_path = _find_pddrc_file(prompts_root)
    if pddrc_path:
        try:
            config = _load_pddrc_config(pddrc_path)
            contexts = config.get("contexts", {})
            if isinstance(contexts, dict):
                for context in contexts.values():
                    if not isinstance(context, dict):
                        continue
                    defaults = context.get("defaults", {})
                    configured = defaults.get("prompts_dir") if isinstance(defaults, dict) else None
                    if isinstance(configured, str) and configured.strip():
                        configured_path = Path(configured.strip())
                        candidates.append(
                            configured_path
                            if configured_path.is_absolute()
                            else project_root / configured_path
                        )
        except (KeyError, TypeError, ValueError):
            pass

    # A narrowed context root (prompts/backend or specs/backend) needs its
    # immediate parent to identify a sibling context such as frontend.
    for candidate in list(candidates):
        if candidate.parent != project_root:
            candidates.append(candidate.parent)

    roots: List[Path] = []
    seen: set[str] = set()
    for candidate in candidates:
        try:
            resolved = candidate.resolve(strict=False)
            resolved.relative_to(project_root)
        except (OSError, RuntimeError, ValueError):
            continue
        key = os.path.normcase(str(resolved))
        if key in seen:
            continue
        seen.add(key)
        roots.append(resolved)
    return tuple(roots)


def _architecture_prompt_owner(
    architecture_filename: PurePosixPath,
    prompt_roots: Tuple[Path, ...],
    active_root: Optional[Path] = None,
) -> Tuple[List[Path], bool]:
    """Return distinct physical prompts and a containment verdict.

    With ``active_root`` the verdict reflects only whether the ACTIVE prompt root's walk
    stayed contained; an escaping same-leaf symlink in an UNRELATED auxiliary root must
    not invalidate a unique contained owner in the active root (only the active context's
    own expected prompt escaping is a hard failure). Without ``active_root`` the verdict is
    the legacy "every walked path was contained".
    """
    owners: Dict[str, Path] = {}
    all_contained = True
    active_contained = True
    active_key: Optional[str] = None
    if active_root is not None:
        try:
            active_key = os.path.normcase(str(Path(active_root).resolve(strict=False)))
        except (OSError, RuntimeError):
            active_key = None
    for root in prompt_roots:
        relative_parts = _prompt_relative_parts_for_root(root, architecture_filename)
        owner, contained = _walk_prompt_relative_path(root, relative_parts)
        if not contained:
            all_contained = False
            if active_key is not None:
                try:
                    if os.path.normcase(str(Path(root).resolve(strict=False))) == active_key:
                        active_contained = False
                except (OSError, RuntimeError):
                    pass
            continue
        if owner is None:
            continue
        try:
            key = os.path.normcase(str(owner.resolve(strict=False)))
        except (OSError, RuntimeError):
            continue
        owners.setdefault(key, owner)
    return list(owners.values()), (active_contained if active_root is not None else all_contained)


def _resolve_context_name_for_basename(
    basename: str,
    context_override: Optional[str] = None,
    pddrc_anchor: Optional[Path] = None,
) -> Optional[str]:
    """Resolve the context for a basename when no explicit override is provided.

    ``pddrc_anchor`` anchors the ``.pddrc`` search at the project instead of the
    process CWD; without it, detecting the context for a path-qualified basename from
    a parent/sibling directory (with an absolute prompts root and no explicit
    override) fails, and the canonical architecture target is missed.
    """
    if context_override:
        return context_override

    pddrc_path = _find_pddrc_file(pddrc_anchor)
    if not pddrc_path:
        return None

    try:
        config = _load_pddrc_config(pddrc_path)
    except ValueError:
        return None

    return _detect_context_from_basename(basename, config, pddrc_path=pddrc_path)


def _prompt_basename_candidates(
    basename: str,
    context_name: Optional[str] = None,
    include_simple_name: bool = False,
    pddrc_anchor: Optional[Path] = None,
) -> List[str]:
    """Return prompt-relative basename candidates ordered from most to least specific."""
    candidates: List[str] = []

    def _add(value: Optional[str]) -> None:
        if value and value not in candidates:
            candidates.append(value)

    _add(basename)

    if context_name:
        _add(_relative_basename_for_context(basename, context_name, pddrc_anchor))

    if include_simple_name:
        _add(basename.split("/")[-1] if "/" in basename else basename)

    return candidates


def _module_filepath_matches_basename(
    module_filepath: Optional[str],
    basename: str,
    context_name: Optional[str] = None,
    pddrc_anchor: Optional[Path] = None,
) -> bool:
    """Return True when a flat architecture filename still clearly maps to a nested basename.

    A path-qualified basename must be a path-SUFFIX of the module filepath. This
    accepts an exact match and legitimately shorter qualified forms
    (``login/page`` -> ``src/app/login/page.tsx``) while rejecting a wrong directory
    (issue #1677: ``foo/login/page`` or ``foo/page`` must NOT map to
    ``src/app/login/page.tsx``, and ``foo/page`` must NOT map to a root ``page.tsx``).
    A single-component (flat) basename keeps leaf matching.
    """
    # Untrusted metadata may carry a non-string filepath; treat it as no match rather
    # than letting Path() raise a TypeError that a broad except swallows into a wrong
    # fallback.
    if not isinstance(module_filepath, str) or not module_filepath:
        return False

    relative_basename = _relative_basename_for_context(basename, context_name, pddrc_anchor)
    basename_parts = tuple(
        part.lower() for part in Path(relative_basename).parts
    )
    filepath_parts = tuple(
        part.lower() for part in Path(module_filepath).with_suffix("").parts
    )
    if not basename_parts or not filepath_parts:
        return False

    # Flat basename: match by leaf only.
    if len(basename_parts) == 1:
        return filepath_parts[-1] == basename_parts[-1]

    # Path-qualified basename: require it to be a full path-suffix of the filepath.
    if len(basename_parts) > len(filepath_parts):
        return False
    return tuple(filepath_parts[-len(basename_parts):]) == tuple(basename_parts)


def _filepath_matches_context(
    normalized: str,
    context_config: Any,
    project_root: Optional[Path] = None,
    *,
    repo_root_output_matches: bool = True,
) -> Optional[bool]:
    """Whether a posix filepath lies in one context's declared territory.

    Returns True/False when the context declares a territory (``paths`` globs or
    configured output locations), or ``None`` when it declares none (no constraint).
    Shared by :func:`_context_owned_filepath` (the resolving context) and
    :func:`_filepath_owned_by_other_context` (sibling contexts).

    ``normalized`` is a project-relative architecture filepath. A context may declare
    ABSOLUTE ``paths`` globs or output paths; those are re-expressed relative to
    ``project_root`` before comparison (an absolute config value outside the project
    can never own a project-relative target). Without this, an absolute
    ``generate_output_path`` never matches and a sibling context stops owning its
    code — re-opening the cross-context borrow this guard blocks.
    """
    if not isinstance(context_config, dict):
        return None

    root_posix = None
    if project_root is not None:
        root_posix = PurePosixPath(str(project_root).replace("\\", "/"))

    # Windows path semantics are case-insensitive. When the project root is a Windows
    # (drive-qualified) path, compare territory case-insensitively so a drive/directory
    # casing difference between .pddrc config and the resolved project root cannot hide
    # sibling ownership. A POSIX root keeps case-sensitive matching (unchanged).
    windows_ci = bool(project_root is not None and PureWindowsPath(str(project_root)).drive)

    def _fold(value: str) -> str:
        return value.lower() if windows_ci else value

    def _project_relative(value: str) -> Optional[str]:
        """Re-express a config path relative to the project; None if unusable."""
        v = value.replace("\\", "/")
        pure = PurePosixPath(v)
        # A Windows drive-qualified value (``C:/x``) is not POSIX-absolute yet is not
        # project-relative either; relativize it against the (equally drive-qualified)
        # project root so sibling-territory detection still fires on Windows instead of
        # silently treating ``C:/proj/frontend`` as a relative literal that matches nothing.
        if not pure.is_absolute() and not PureWindowsPath(value).drive:
            # Normalize a relative value (strip leading ``./``, collapse ``//``) so a
            # ``./frontend/**`` glob compares equal to the normalized project-relative
            # architecture filepath instead of silently missing.
            return pure.as_posix()
        if root_posix is None:
            return None
        try:
            return pure.relative_to(root_posix).as_posix()
        except ValueError:
            if windows_ci:
                # Retry case-insensitively so ``C:/Proj/frontend`` relativizes against a
                # ``c:/proj`` root; comparisons below fold both sides, so the lowered tail
                # is fine.
                try:
                    return PurePosixPath(v.lower()).relative_to(
                        PurePosixPath(str(root_posix).lower())
                    ).as_posix()
                except ValueError:
                    return None
            return None  # absolute path outside the project — cannot own it

    globs = [p for p in context_config.get("paths", []) if isinstance(p, str) and p]
    prefixes: List[str] = []
    defaults = context_config.get("defaults", {})
    if isinstance(defaults, dict):
        for key in ("generate_output_path", "test_output_path", "example_output_path"):
            value = defaults.get(key)
            if isinstance(value, str) and value.strip():
                prefixes.append(value)
        outputs = defaults.get("outputs", {})
        if isinstance(outputs, dict):
            for spec in outputs.values():
                template = spec.get("path") if isinstance(spec, dict) else None
                if isinstance(template, str) and template.strip():
                    prefixes.append(template)

    if not globs and not prefixes:
        return None

    normalized_cmp = _fold(normalized)
    for pattern in globs:
        pattern_norm = _project_relative(pattern)
        if pattern_norm is None:
            continue
        pattern_cmp = _fold(pattern_norm)
        base = pattern_cmp.rstrip("*").rstrip("/")
        if (
            fnmatch.fnmatch(normalized_cmp, pattern_cmp)
            or normalized_cmp == base
            or (base and normalized_cmp.startswith(base + "/"))
        ):
            return True

    for prefix in prefixes:
        # Output templates such as "backend/functions/{name}.py" contribute only
        # the directory before the first placeholder.
        prefix_head = prefix.replace("\\", "/")
        if "{" in prefix_head:
            prefix_head = prefix_head.split("{", 1)[0]
        prefix_norm = _project_relative(prefix_head)
        if prefix_norm is None:
            continue
        base = _fold(prefix_norm.strip().rstrip("/"))
        if base.startswith("./"):
            base = base[2:]
        if base in ("", "."):
            # A repo-root output path imposes no territory constraint.
            if repo_root_output_matches:
                return True
            continue
        if normalized_cmp == base or normalized_cmp.startswith(base + "/"):
            return True

    return False


_TERRITORY_CONFIG_UNSET: Any = object()
# Distinct from ``None`` (no .pddrc at all): a .pddrc was found but could not be parsed.
_TERRITORY_MALFORMED: Any = object()


def _filepath_in_named_context(
    architecture_filepath: Optional[str],
    config: Any,
    project_root: Optional[Path] = None,
) -> bool:
    """True when the filepath lies in ANY named (non-``default``) context's territory.

    Used when the resolving context cannot be established: a heuristic borrow whose
    target sits in some named context may pair the prompt with a sibling context's code,
    so it must be denied even though there is no single resolving context to exclude.
    """
    if not isinstance(architecture_filepath, str) or not architecture_filepath.strip():
        return False
    if not isinstance(config, dict):
        return False
    contexts = config.get("contexts", {})
    if not isinstance(contexts, dict):
        return False
    normalized = PurePosixPath(architecture_filepath.strip().replace("\\", "/")).as_posix()
    for other_name, other_config in contexts.items():
        if other_name == "default":
            continue
        if _filepath_matches_context(
            normalized, other_config, project_root, repo_root_output_matches=False
        ) is True:
            return True
    return False


def _filepath_owned_by_other_context(
    architecture_filepath: Optional[str],
    context_name: Optional[str],
    pddrc_anchor: Optional[Path] = None,
    *,
    config_snapshot: Any = _TERRITORY_CONFIG_UNSET,
    project_root: Optional[Path] = None,
) -> bool:
    """True when the filepath lies in the territory of a DIFFERENT named context.

    A PROVEN-owner architecture row (its physical prompt IS the resolved prompt) may
    legitimately target code outside its own context's globs — e.g. an intentionally
    shared path owned by no context. It must still be rejected when that target
    belongs to a SIBLING context, which is the stale cross-context borrow. The
    catch-all ``default`` context is ignored so a shared path it happens to match does
    not read as foreign ownership.
    """
    if not isinstance(architecture_filepath, str) or not architecture_filepath.strip():
        return False
    if not context_name:
        return False
    if config_snapshot is _TERRITORY_CONFIG_UNSET:
        pddrc_path = _find_pddrc_file(pddrc_anchor)
        if not pddrc_path:
            return False
        try:
            config = _load_pddrc_config(pddrc_path)
        except (ValueError, KeyError, TypeError):
            return False
        project_root = pddrc_path.parent
    else:
        config = config_snapshot
    if not isinstance(config, dict):
        return False
    contexts = config.get("contexts", {})
    if not isinstance(contexts, dict):
        return False
    normalized = PurePosixPath(architecture_filepath.strip().replace("\\", "/")).as_posix()
    for other_name, other_config in contexts.items():
        if other_name == context_name or other_name == "default":
            continue
        if _filepath_matches_context(
            normalized,
            other_config,
            project_root,
            repo_root_output_matches=False,
        ) is True:
            return True
    return False


def _context_owned_filepath(
    architecture_filepath: Optional[str],
    context_name: Optional[str],
    pddrc_anchor: Optional[Path] = None,
    *,
    config_snapshot: Any = _TERRITORY_CONFIG_UNSET,
    project_root: Optional[Path] = None,
) -> bool:
    """Return True when a borrowed architecture filepath is inside a context's territory.

    Leaf- and filepath-stem-matched architecture entries are heuristic borrows:
    unlike an exact filename match, they do not directly name the resolved prompt.
    A stale sibling-context entry (e.g. a ``frontend`` module whose prompt was
    deleted but whose ``architecture.json`` row survives) can otherwise be borrowed
    by a same-leaf ``backend`` prompt and silently redirect the sync onto the
    foreign module's code. Restrict such borrows to filepaths the resolving
    prompt's context owns — its ``paths`` globs or configured output locations.

    ``pddrc_anchor`` anchors the ``.pddrc`` lookup at the project (the directory of
    ``architecture.json``), NOT the process CWD. Resolution is frequently invoked
    from a parent/sibling working directory with an absolute prompts root, and a
    CWD-based lookup would miss the project's ``.pddrc`` and fail open — re-opening
    the very cross-context borrow this guard exists to block.

    Returns True (permit) whenever no territory can be derived: a bare basename
    with no resolvable context, a missing/invalid ``.pddrc``, or a repo-root output
    path. Non-context projects therefore keep the prior, permissive behavior.
    """
    if not isinstance(architecture_filepath, str) or not architecture_filepath.strip():
        return True
    if not context_name:
        return True
    if config_snapshot is _TERRITORY_CONFIG_UNSET:
        pddrc_path = _find_pddrc_file(pddrc_anchor)
        if not pddrc_path:
            return True
        try:
            config = _load_pddrc_config(pddrc_path)
        except (ValueError, KeyError, TypeError):
            return True
        project_root = pddrc_path.parent
    else:
        config = config_snapshot
    if not isinstance(config, dict):
        return True
    contexts = config.get("contexts", {})
    context_config = contexts.get(context_name) if isinstance(contexts, dict) else None
    if not isinstance(context_config, dict):
        return True

    normalized = PurePosixPath(
        architecture_filepath.strip().replace("\\", "/")
    ).as_posix()

    match = _filepath_matches_context(normalized, context_config, project_root)
    # No territory declared for this context — impose no restriction.
    return True if match is None else match


def _anchor_output_paths_at_project(result: Dict[str, Any], project_root: Path) -> Dict[str, Any]:
    """Resolve relative output artifact paths against the project root, not the CWD.

    Template-generated code/example/test paths are project-relative; a resolution
    run from a parent/sibling working directory must still write under the project.
    When the project root IS the CWD the relative paths already resolve correctly, so
    they are left as-is to preserve the established (relative) return contract; only a
    differing CWD triggers re-anchoring. Absolute paths and the already-resolved
    ``prompt`` key are unchanged.
    """
    try:
        if project_root.resolve(strict=False) == Path.cwd().resolve():
            return result
    except (OSError, RuntimeError):
        pass

    def _anchor(value: Any) -> Any:
        if isinstance(value, Path) and not value.is_absolute():
            return project_root / value
        return value

    anchored: Dict[str, Any] = {}
    for key, value in result.items():
        if key == "prompt":
            anchored[key] = value
        elif isinstance(value, list):
            anchored[key] = [_anchor(item) for item in value]
        else:
            anchored[key] = _anchor(value)
    return anchored


def _overlay_configured_output_paths(
    result: Dict[str, Path],
    outputs_config: Dict[str, Any],
    output_paths: Dict[str, str],
    basename: str,
    language: str,
    context_name: Optional[str] = None,
    pddrc_anchor: Optional[Path] = None,
) -> Dict[str, Path]:
    """Overlay construct_paths-derived output locations onto template-derived paths."""
    merged = dict(result)

    code_path = output_paths.get("generate_output_path") or output_paths.get("output") or output_paths.get("code_file")
    if "code" not in outputs_config and code_path:
        relative_basename = _relative_basename_for_context(basename, context_name, pddrc_anchor)
        dir_prefix, name_part = _extract_name_part(relative_basename)
        extension = get_extension(language)
        code_path_obj = Path(code_path)
        if code_path.endswith("/") or code_path_obj.suffix == "":
            merged["code"] = code_path_obj / dir_prefix / f"{name_part}{_dot(extension)}"
        else:
            merged["code"] = code_path_obj

    return merged


def _prompt_candidate_within_root(candidate: Path, resolved_root: Path) -> bool:
    """True when ``candidate`` resolves inside ``resolved_root``.

    Recursive prompt discovery follows symlinks, so a same-leaf in-root symlink can
    point at an external file. Returning such a candidate lets an update operation
    write through it and overwrite a file outside the repository. Every recursively
    discovered candidate must therefore pass this containment check before it is
    returned, mirroring the guarded search in
    ``_resolve_prompt_path_from_architecture``.
    """
    try:
        candidate.resolve(strict=False).relative_to(resolved_root)
        return True
    except (OSError, RuntimeError, ValueError):
        return False


# Sentinel distinguishing "read architecture.json from disk" from an explicit
# (possibly empty) pre-parsed module snapshot. get_pdd_file_paths parses the
# architecture ONCE and threads that immutable snapshot through prompt discovery
# and code-path selection so a mid-resolution rewrite of architecture.json cannot
# produce a torn prompt/code pair (prompt from the old registry, code from the new).
_ARCH_MODULES_UNSET: Any = object()

# Three-state result of architecture-row ownership relative to the resolved prompt.
# INELIGIBLE: the row demonstrably names a DIFFERENT prompt (or is unsafe metadata).
# ELIGIBLE:   a heuristic match with no proven physical owner (canonical / absent) —
#             additionally constrained to the resolving context's territory.
# PROVEN:     the row's physical prompt owner IS the resolved prompt (explicit
#             mapping) — trusted even when its code target is outside the context's
#             own globs, so long as it is not owned by a SIBLING context.
_OWNERSHIP_INELIGIBLE = 0
_OWNERSHIP_ELIGIBLE = 1
_OWNERSHIP_PROVEN = 2


def _find_prompt_file(
    basename: str,
    language: str,
    prompts_root: Path,
    architecture_path: Optional[Path] = None,
    context_override: Optional[str] = None,
    arch_modules: Any = _ARCH_MODULES_UNSET,
) -> Optional[Path]:
    """Authoritative prompt file resolution — case-insensitive, subdirectory-aware.

    Single source of truth for finding prompt files on disk. Handles:
    - Case-sensitive filesystems (Linux): _Python vs _python
    - Nested subdirectories: prompts/src/clients/foo_Python.prompt
    - Architecture.json filename hints with correct casing
    - Glob metacharacters in basenames: [id], (group)
    - Execution from temp directories (/tmp/pdd_job_xxx)
    - Context-aware scoping via context_override

    Resolution cascade (fast → expensive):
    1. Direct path in prompts_root
    2. Case-insensitive match in prompts_root
    3. Architecture.json hint → recursive case-insensitive search
    4. Recursive glob fallback across all subdirectories

    When multiple matches exist, context_override (via .pddrc prompts_dir)
    is used to prefer matches within the correct context subdirectory.

    Returns:
        Actual filesystem Path with correct casing, or None if not found.
    """
    if _safe_architecture_prompt_filename(basename) is None:
        raise UnsafePromptPathError(Path(basename), prompts_root.resolve(strict=False))
    if _safe_prompt_language(language) is None:
        raise UnsafePromptPathError(Path(str(language)), prompts_root.resolve(strict=False))
    name = basename.split('/')[-1] if '/' in basename else basename
    # Containment anchor for recursive discovery AND the CWD-independent .pddrc anchor
    # for context detection / prefix stripping: resolution is often driven from a
    # parent/sibling directory with an absolute (possibly custom) prompts root.
    resolved_prompts_root = prompts_root.resolve(strict=False)
    context_name = _resolve_context_name_for_basename(
        basename, context_override, pddrc_anchor=resolved_prompts_root
    )
    basename_candidates = _prompt_basename_candidates(
        basename,
        context_name=context_name,
        include_simple_name="/" not in basename,
        pddrc_anchor=resolved_prompts_root,
    )

    # Resolve context prefix from .pddrc for scoping recursive searches.
    # e.g., context 'backend-utils' with prompts_dir='prompts/backend/utils'
    # yields context_prefix='backend/utils' so we prefer matches under that path.
    context_prefix = None
    if context_name:
        # Anchor at the prompt root, NOT the process CWD: resolution is often driven
        # from a parent/sibling directory with an absolute prompts root, and a
        # CWD-based lookup would miss the project's .pddrc, drop context_prefix, and
        # let a same-leaf prompt in the WRONG context win the shallowest/lexicographic
        # tie-break below.
        pddrc_path = _find_pddrc_file(resolved_prompts_root)
        if pddrc_path:
            try:
                config = _load_pddrc_config(pddrc_path)
                context_config = config.get('contexts', {}).get(context_name, {})
                prompts_dir_config = context_config.get('defaults', {}).get('prompts_dir', '')
                if prompts_dir_config:
                    context_prefix = _context_prefix_for_prompts_root(
                        prompts_dir_config,
                        pddrc_path,
                        resolved_prompts_root,
                    )
            except (ValueError, KeyError):
                pass

    # --- Step 1: Direct path (fast path for simple/flat projects) ---
    # Containment applies to the fast path too: the exact expected prompt may itself
    # be a file symlink whose target escapes prompts_root. An in-root alias resolves
    # inside the root and is preserved; an escaping symlink is skipped so a later
    # update cannot open it with "w" and truncate the external target.
    for candidate_basename in basename_candidates:
        direct_relative = PurePosixPath(
            f"{candidate_basename}_{language}.prompt"
        )
        direct_candidate = prompts_root.joinpath(*direct_relative.parts)
        if context_prefix and not _prompt_path_has_context_prefix(
            direct_candidate, prompts_root, context_prefix
        ):
            continue
        resolved, contained = _walk_prompt_relative_path(
            prompts_root,
            tuple(direct_relative.parts),
        )
        if not contained:
            raise UnsafePromptPathError(
                direct_candidate,
                resolved_prompts_root,
            )
        if resolved:
            return resolved

    # --- Step 3: Architecture.json hint → recursive search ---
    # Use the caller's immutable module snapshot when provided so prompt discovery
    # and code-path selection agree on ONE architecture view; only re-check the file
    # on disk when no snapshot was threaded in.
    have_architecture = architecture_path is not None and (
        arch_modules is not _ARCH_MODULES_UNSET or architecture_path.exists()
    )
    if have_architecture:
        # Pass the resolved context so the architecture hint respects context
        # territory: with a broad prompts root, a bare-leaf lookup must NOT borrow a
        # sibling context's row (e.g. a backend resolution picking up a
        # frontend/credits row) and return its prompt before the context-aware
        # recursive fallback runs. _context_owned_filepath rejects the foreign row.
        _, arch_filename = _get_filepath_from_architecture(
            architecture_path,
            f"{basename_candidates[0]}_{language}.prompt",
            basename=basename,
            language=language,
            modules=arch_modules,
            resolved_context_name=context_name,
        )
        if arch_filename:
            # 3a: Direct join (handles architecture filenames with subdirectory paths)
            joined = _resolve_prompt_path_from_architecture(
                prompts_root,
                arch_filename,
                context_prefix=context_prefix,
                basename=basename,
            )
            if joined is None:
                arch_filename = None
        if arch_filename and joined is not None:
            resolved_joined = _case_insensitive_path_lookup(joined)
            if resolved_joined and _prompt_candidate_within_root(
                resolved_joined, resolved_prompts_root
            ):
                return resolved_joined
            # 3b: Case-insensitive in the joined parent directory
            if joined.parent.is_dir():
                joined_lower = joined.name.lower()
                for candidate in joined.parent.iterdir():
                    if (
                        candidate.is_file()
                        and candidate.name.lower() == joined_lower
                        and _prompt_candidate_within_root(candidate, resolved_prompts_root)
                    ):
                        return candidate
            # 3c: Recursive search for the architecture filename in all subdirectories.
            # Collect all matches and pick shallowest deterministically. Every match
            # must resolve inside prompts_root so a same-leaf symlink cannot escape.
            arch_basename_lower = Path(arch_filename).name.lower()
            arch_matches = []
            unsafe_arch_matches = []
            for candidate in prompts_root.rglob("*.prompt"):
                if not candidate.is_file() or candidate.name.lower() != arch_basename_lower:
                    continue
                if not _prompt_candidate_aligns_basename(candidate, basename):
                    continue
                if _prompt_candidate_within_root(candidate, resolved_prompts_root):
                    arch_matches.append(candidate)
                else:
                    unsafe_arch_matches.append(candidate)
            if arch_matches and context_prefix:
                arch_matches = [
                    m for m in arch_matches
                    if _prompt_path_has_context_prefix(
                        m, prompts_root, context_prefix
                    )
                ]
            if arch_matches:
                if len(arch_matches) > 1:
                    # Then prefer match matching directory hint from basename
                    dir_hint = basename.rsplit('/', 1)[0] if '/' in basename else None
                    if dir_hint and len(arch_matches) > 1:
                        hint_filtered = [m for m in arch_matches if dir_hint in str(m)]
                        if hint_filtered:
                            arch_matches = hint_filtered
                arch_matches.sort(key=lambda p: (len(p.parts), str(p)))
                return arch_matches[0]
            if unsafe_arch_matches:
                relevant_unsafe = unsafe_arch_matches
                if context_prefix:
                    relevant_unsafe = [
                        candidate for candidate in unsafe_arch_matches
                        if _prompt_path_has_context_prefix(
                            candidate, prompts_root, context_prefix
                        )
                    ]
                if relevant_unsafe:
                    raise UnsafePromptPathError(
                        relevant_unsafe[0], resolved_prompts_root
                    )

    # --- Step 4: Recursive glob fallback (always works) ---
    # Case-insensitive on both basename and language suffix.
    # rglob("*.prompt") + manual filtering because rglob patterns are
    # case-sensitive on Linux, so we can't rely on the glob pattern for
    # basenames like "dashboard" vs on-disk "Dashboard".
    lang_lower = language.lower()
    matches = []
    unsafe_matches = []
    # Filter by the cheap filename leaf FIRST, then pay the containment resolve only for
    # the handful of leaf-matching candidates — not once per prompt in the whole tree.
    expected_leaves = {
        f"{candidate_basename.split('/')[-1].lower()}_{lang_lower}.prompt"
        for candidate_basename in basename_candidates
    }
    for candidate in prompts_root.rglob("*.prompt"):
        if not candidate.is_file():
            continue
        if candidate.name.lower() not in expected_leaves:
            continue
        # A leaf-matching candidate that escapes prompts_root through a symlink is
        # recorded as unsafe; an in-root match is used.
        if not _prompt_candidate_within_root(candidate, resolved_prompts_root):
            unsafe_matches.append(candidate)
            continue
        matches.append(candidate)
    if matches and context_prefix:
        matches = [
            m for m in matches
            if _prompt_path_has_context_prefix(m, prompts_root, context_prefix)
        ]
    if matches:
        # Issue #1677: a path-qualified basename (e.g. `app/login/page`) must resolve
        # to a prompt WITHIN its own directory. Do not fall back to a same-leaf prompt
        # in a different directory — that silently syncs the wrong module for a
        # mistyped/foreign path like `foo/page`. The basename must be a path-SUFFIX of
        # the match's module path (its absolute directory plus the module leaf). Using
        # the absolute path means a deep prompts_dir or a context whose directories are
        # already part of prompts_root still matches, while an unrelated directory does
        # not (and `foo` inside an absolute prefix like /home/foo cannot false-match,
        # since only the suffix is compared).
        if "/" in basename:
            basename_variants = {
                tuple(part.lower() for part in Path(basename).parts)
            }
            relative_basename = _relative_basename_for_context(
                basename, context_name, resolved_prompts_root
            )
            if relative_basename != basename:
                basename_variants.add(
                    tuple(part.lower() for part in Path(relative_basename).parts)
                )
            aligned = []
            for m in matches:
                module_leaf = extract_module_from_include(m.name) or m.stem
                module_parts = tuple(
                    part.lower() for part in m.parent.parts + (module_leaf,)
                )
                if any(
                    len(bp) <= len(module_parts) and tuple(module_parts[-len(bp):]) == bp
                    for bp in basename_variants
                ):
                    aligned.append(m)
            if not aligned:
                return None
            matches = aligned
        matches.sort(key=lambda p: (len(p.parts), str(p)))
        return matches[0]
    if unsafe_matches:
        relevant_unsafe = unsafe_matches
        if context_prefix:
            relevant_unsafe = [
                candidate for candidate in unsafe_matches
                if _prompt_path_has_context_prefix(
                    candidate, prompts_root, context_prefix
                )
            ]
        if "/" in basename and relevant_unsafe:
            # An escaping same-leaf symlink under an UNRELATED directory must not hard-fail
            # a path-qualified creation: restrict the hard failure to unsafe candidates that
            # actually align with the requested basename's directory suffix, exactly as the
            # safe matches above are aligned.
            _bn_variants = {tuple(p.lower() for p in Path(basename).parts)}
            _rel_bn = _relative_basename_for_context(basename, context_name, resolved_prompts_root)
            if _rel_bn != basename:
                _bn_variants.add(tuple(p.lower() for p in Path(_rel_bn).parts))

            def _unsafe_aligns(cand: Path) -> bool:
                leaf = extract_module_from_include(cand.name) or cand.stem
                parts = tuple(p.lower() for p in cand.parent.parts + (leaf,))
                return any(
                    len(bp) <= len(parts) and tuple(parts[-len(bp):]) == bp
                    for bp in _bn_variants
                )

            relevant_unsafe = [c for c in relevant_unsafe if _unsafe_aligns(c)]
        if relevant_unsafe:
            raise UnsafePromptPathError(relevant_unsafe[0], resolved_prompts_root)

    return None


def _get_filepath_from_architecture(
    architecture_path: Path,
    prompt_filename: str,
    basename: Optional[str] = None,
    language: Optional[str] = None,
    prompt_path: Optional[Path] = None,
    prompts_root: Optional[Path] = None,
    prompt_roots: Optional[Tuple[Path, ...]] = None,
    resolved_context_name: Optional[str] = None,
    modules: Any = _ARCH_MODULES_UNSET,
) -> Tuple[Optional[str], Optional[str]]:
    """Extract filepath for a prompt from architecture.json.

    Looks up the module in architecture.json that matches the given prompt
    filename and returns its filepath field if present.

    Args:
        architecture_path: Path to architecture.json file.
        prompt_filename: The prompt filename to search for (e.g., "models_findings_Python.prompt").
        basename: Optional basename for alternative matching (e.g., "models_findings").
        language: Optional language for alternative matching (e.g., "Python").
        prompt_path: Resolved physical prompt, used to reject an architecture
            entry that directly names a different same-leaf prompt.
        prompts_root: Root used to resolve architecture prompt filenames.
        prompt_roots: Contained prompt roots used to establish physical
            ownership across sibling contexts without recursive scans.
        resolved_context_name: The resolving prompt's ``.pddrc`` context. Restricts
            heuristic leaf/filepath-stem borrows to that context's territory so a
            stale sibling-context entry cannot redirect the sync (see
            :func:`_context_owned_filepath`).
        modules: Pre-parsed architecture module snapshot. When left unset the file
            is read from disk; when supplied (even as ``None``/empty) it is used
            as-is so caller-shared resolution reads ONE immutable architecture view.

    Returns:
        Tuple of (filepath, matched_filename) if found, else (None, None).

    Supports both architecture.json formats:
        - {"modules": [...]} - nested structure
        - [...] - flat array
    """
    try:
        if modules is _ARCH_MODULES_UNSET:
            with open(architecture_path, 'r', encoding='utf-8') as f:
                arch = json.load(f)
            modules = extract_modules(arch)

        if not modules:
            return None, None

        # Prefer the caller's resolved context (CWD-independent) over re-detecting it
        # from the CWD: a resolution driven from a parent/sibling directory would
        # otherwise mis-detect the context, mis-strip the basename prefix, and miss a
        # canonical path-qualified architecture target (falling back to the default).
        context_name = resolved_context_name or (
            _resolve_context_name_for_basename(basename) if basename else None
        )
        pddrc_anchor = architecture_path.parent if architecture_path is not None else None
        territory_config: Any = None
        territory_project_root: Optional[Path] = None
        territory_pddrc = _find_pddrc_file(pddrc_anchor)
        if territory_pddrc:
            try:
                territory_config = _load_pddrc_config(territory_pddrc)
                territory_project_root = territory_pddrc.parent
            except (ValueError, KeyError, TypeError):
                # Present but unparseable: mark it so a heuristic borrow (which needs
                # territory to be confined) is denied rather than falling open to the
                # permissive "no territory" behavior.
                territory_config = _TERRITORY_MALFORMED
                territory_project_root = territory_pddrc.parent

        # Issue #1677: a path-qualified basename (e.g. `foo/page`) must only match a
        # module whose filepath aligns with its directory. Otherwise an exact match on
        # a bare leaf filename (`page_*.prompt`) silently resolves a mistyped/foreign
        # path to an unrelated same-leaf module. Flat basenames are unaffected (their
        # ambiguity is already handled upstream).
        path_qualified = bool(basename) and "/" in basename

        def _aligns(module: Dict[str, Any]) -> bool:
            if not path_qualified:
                return True
            return _module_filepath_matches_basename(
                module.get("filepath"), basename, context_name=context_name,
                pddrc_anchor=pddrc_anchor,
            )

        def _belongs_to_resolved_prompt(module: Dict[str, Any]) -> int:
            """Classify a row's ownership relative to the resolved prompt.

            Returns one of ``_OWNERSHIP_INELIGIBLE`` / ``_OWNERSHIP_ELIGIBLE`` /
            ``_OWNERSHIP_PROVEN``. A flat prompt and a nested prompt can share a
            basename; the nested architecture filename is useful when the nested
            ``prompts_dir`` strips that prefix, but it must not be borrowed by the flat
            sibling. A direct, existing architecture-derived prompt path is
            authoritative evidence (PROVEN) of which physical prompt owns the entry.
            Canonical filepath-derived names may not exist as prompt paths, so those
            stay ELIGIBLE for the unique-filepath fallback (still territory-guarded).
            """
            module_filename = module.get("filename")
            if not isinstance(module_filename, str) or not module_filename:
                # Architecture source-file entries without prompt-style names
                # are eligible for the filepath-stem compatibility fallback.
                return _OWNERSHIP_ELIGIBLE
            normalized_filename = _safe_architecture_prompt_filename(module_filename)
            if normalized_filename is None:
                return _OWNERSHIP_INELIGIBLE

            # Validation must precede this context-free discovery return. The
            # caller may not have found a physical prompt yet, but unsafe
            # architecture metadata must already be ineligible as a hint.
            if prompt_path is None or prompts_root is None:
                return _OWNERSHIP_ELIGIBLE

            # Non-prompt source filenames have no prompt ownership identity;
            # their compatibility behavior is governed by filepath stem.
            if not extract_module_from_include(normalized_filename.name):
                return _OWNERSHIP_ELIGIBLE

            roots = prompt_roots or (prompts_root.resolve(strict=False),)
            owners, all_contained = _architecture_prompt_owner(
                normalized_filename,
                roots,
                active_root=prompts_root,
            )
            if not all_contained:
                return _OWNERSHIP_INELIGIBLE
            if not owners:
                # Canonical filepath-derived names need not exist physically as
                # prompt paths, so absence of an owner remains eligible.
                return _OWNERSHIP_ELIGIBLE
            # ``owners`` were obtained by contained directory walks above. Map
            # the prompt's validated root-relative identity across trusted roots
            # so aliases such as ``prompts -> pdd/prompts`` compare correctly.
            # Keep the prompt side lexical: resolving caller-influenced ``prompt_path``
            # here would turn it into a filesystem sink.
            try:
                relative_prompt = prompt_path.relative_to(prompts_root)
            except ValueError:
                return _OWNERSHIP_INELIGIBLE
            if relative_prompt.is_absolute() or ".." in relative_prompt.parts:
                return _OWNERSHIP_INELIGIBLE
            # Project ONLY across roots that ALIAS the resolving prompt root (resolve to
            # the same directory) — never across sibling context roots. Otherwise a
            # uniquely-named SIBLING prompt sitting at the same relative path under a
            # different root is misread as the resolved prompt's proven owner and lends
            # its shared code target across contexts. Resolving the ROOT directories (not
            # the caller-influenced prompt) is safe.
            try:
                prompts_root_key = os.path.normcase(str(prompts_root.resolve(strict=False)))
            except (OSError, RuntimeError):
                return _OWNERSHIP_INELIGIBLE
            alias_roots = []
            for root in roots:
                try:
                    if os.path.normcase(str(Path(root).resolve(strict=False))) == prompts_root_key:
                        alias_roots.append(root)
                except (OSError, RuntimeError):
                    continue
            if not alias_roots:
                alias_roots = [prompts_root]
            expected_keys = {
                os.path.normcase(
                    os.path.abspath(os.path.normpath(root.joinpath(relative_prompt)))
                )
                for root in alias_roots
            }
            owner_keys = {
                os.path.normcase(os.path.abspath(os.path.normpath(owner)))
                for owner in owners
            }
            if not owner_keys.issubset(expected_keys):
                return _OWNERSHIP_INELIGIBLE
            # PROVEN requires a UNIQUE physical owner. When a flat/same-leaf filename
            # matches distinct prompts in more than one context root, the row does not
            # unambiguously identify the resolved prompt, so it stays territory-guarded
            # (ELIGIBLE) rather than letting two contexts both claim one shared target.
            if len(owners) != 1:
                return _OWNERSHIP_ELIGIBLE
            return _OWNERSHIP_PROVEN

        borrow_ownership_cache: Dict[Tuple[str, str], bool] = {}

        def _borrow_ownership_ok(module: Dict[str, Any]) -> bool:
            """Eligibility for an architecture row in the resolving context.

            A PROVEN row (physical owner IS the resolved prompt) is an explicit
            mapping: trusted even when its code target lies outside the context's own
            territory, UNLESS that target belongs to a sibling context (a stale
            cross-context row). A merely ELIGIBLE (heuristic) row is confined to the
            resolving context's own territory.
            """
            filepath = module.get("filepath")
            cache_key = (
                str(module.get("filename") or ""),
                str(filepath or ""),
            )
            cached = borrow_ownership_cache.get(cache_key)
            if cached is not None:
                return cached

            root_resolved = architecture_path.parent.resolve(strict=False)
            contained = (
                _contained_architecture_code_path(root_resolved, filepath)
                if isinstance(filepath, str)
                else None
            )
            if contained is None:
                borrow_ownership_cache[cache_key] = False
                return False

            # Sibling-territory ownership is checked against BOTH the lexical
            # filepath and its RESOLVED project-relative identity. An in-project
            # symlink (e.g. ``backend/link`` -> ``frontend/src``) passes project
            # containment yet physically lands in a sibling context; a lexical-only
            # check would let that alias smuggle a code target into the sibling.
            identities = [filepath]
            try:
                resolved_rel = contained.relative_to(root_resolved).as_posix()
            except ValueError:
                resolved_rel = None
            if resolved_rel and resolved_rel != PurePosixPath(
                filepath.replace("\\", "/")
            ).as_posix():
                identities.append(resolved_rel)
            if any(
                _filepath_owned_by_other_context(
                    identity,
                    resolved_context_name,
                    pddrc_anchor,
                    config_snapshot=territory_config,
                    project_root=territory_project_root,
                )
                for identity in identities
            ):
                borrow_ownership_cache[cache_key] = False
                return False
            context_owned = _context_owned_filepath(
                filepath,
                resolved_context_name,
                pddrc_anchor,
                config_snapshot=territory_config,
                project_root=territory_project_root,
            )
            ownership = _belongs_to_resolved_prompt(module)
            if ownership == _OWNERSHIP_INELIGIBLE:
                borrow_ownership_cache[cache_key] = False
                return False
            # A heuristic (non-proven) borrow is only safe if it can be confined to the
            # resolving context's territory. When the .pddrc defining that territory is
            # present but UNPARSEABLE, confinement cannot be verified — deny the heuristic
            # borrow (fail closed) instead of falling open to the permissive default. A
            # proven, explicit prompt->code mapping is still honored.
            if territory_config is _TERRITORY_MALFORMED and ownership != _OWNERSHIP_PROVEN:
                borrow_ownership_cache[cache_key] = False
                return False
            # When the resolving context cannot be established (no override and the
            # basename does not encode one), a FOREIGN heuristic borrow — one whose
            # architecture filename does not name this module (matched only by a leaf/stem
            # collision) — whose target lies in ANY named context may pair this prompt with
            # a sibling context's code. Deny it (fail closed). A row that names this module
            # (even with no physical prompt yet), a proven mapping, and a genuinely
            # unowned/shared target are still allowed.
            # A row whose architecture filename EXACTLY names the requested module is that
            # module's own explicit mapping, even if no physical prompt exists yet (new
            # module) — distinct from a foreign leaf/stem collision.
            row_names_this_module = (
                str(module.get("filename") or "").strip().lower() == prompt_filename.strip().lower()
            )
            if (
                resolved_context_name is None
                and ownership != _OWNERSHIP_PROVEN
                and not row_names_this_module
                and isinstance(territory_config, dict)
                and any(
                    _filepath_in_named_context(identity, territory_config, territory_project_root)
                    for identity in identities
                )
            ):
                borrow_ownership_cache[cache_key] = False
                return False
            # The exact current-module row is honored even when its (safe, non-sibling)
            # target is shared/unowned and no physical prompt exists yet: sibling-owned and
            # unsafe targets were already rejected above, so this cannot cross contexts.
            allowed = (
                context_owned
                or ownership == _OWNERSHIP_PROVEN
                or row_names_this_module
            )
            borrow_ownership_cache[cache_key] = allowed
            return allowed

        # Try exact filename match first
        for module in modules:
            if not isinstance(module, dict):
                continue
            if (
                module.get("filename") == prompt_filename
                and _aligns(module)
                and _borrow_ownership_ok(module)
            ):
                return module.get("filepath"), module.get("filename")

        # Try case-insensitive filename match. A module may carry ``"filename": null``
        # (identified only by filepath); coerce to a string so .lower() never raises
        # AttributeError, which the broad get_pdd_file_paths fallback would otherwise
        # swallow into a cwd-relative default path.
        prompt_filename_lower = prompt_filename.lower()
        for module in modules:
            if not isinstance(module, dict):
                continue
            if (
                str(module.get("filename") or "").lower() == prompt_filename_lower
                and _aligns(module)
                and _borrow_ownership_ok(module)
            ):
                return module.get("filepath"), module.get("filename")

        def _unique_match(candidates: List[Dict[str, Any]]) -> Tuple[Optional[str], Optional[str]]:
            """Return one output identity, never first-match-wins across outputs."""
            by_filepath: Dict[str, Dict[str, Any]] = {}
            for candidate in candidates:
                filepath = candidate.get("filepath")
                if not isinstance(filepath, str) or not filepath.strip():
                    continue
                by_filepath.setdefault(PurePosixPath(filepath).as_posix(), candidate)
            if len(by_filepath) != 1:
                return None, None
            matched = next(iter(by_filepath.values()))
            return matched.get("filepath"), matched.get("filename")

        # A nested .pddrc may make the caller's prompt key relative to a deeper
        # prompts_dir than architecture.json uses. Match a UNIQUE filename leaf
        # instead of assuming the repository prompt root is literally `prompts/`.
        # Path-qualified basenames remain guarded by filepath alignment, and a bare
        # ambiguous leaf is rejected by _architecture_module_choices before this
        # helper is called from get_pdd_file_paths.
        prompt_leaf_lower = PurePosixPath(prompt_filename.replace("\\", "/")).name.lower()
        leaf_match = _unique_match([
            module
            for module in modules
            if isinstance(module, dict)
            and PurePosixPath(
                str(module.get("filename", "")).replace("\\", "/")
            ).name.lower() == prompt_leaf_lower
            and _aligns(module)
            and _borrow_ownership_ok(module)
        ])
        if leaf_match[0]:
            return leaf_match

        # Try basename + language match if provided
        if basename and language:
            basename_candidates = _prompt_basename_candidates(
                basename,
                context_name=context_name,
                include_simple_name="/" not in basename,
                pddrc_anchor=pddrc_anchor,
            )

            for candidate_basename in basename_candidates:
                expected_filename = f"{candidate_basename}_{language}.prompt"
                expected_filename_lower = expected_filename.lower()
                for module in modules:
                    if not isinstance(module, dict):
                        continue
                    module_filename = str(module.get("filename") or "")
                    if (
                        module_filename.lower() == expected_filename_lower
                        and _aligns(module)
                        and _borrow_ownership_ok(module)
                    ):
                        return module.get("filepath"), module.get("filename")

            # Nested basenames must not borrow an unrelated flat architecture entry.
            # Only accept a flat filename match when the module filepath also aligns
            # with the basename tail (e.g. github/page -> .../github/page.tsx).
            if "/" in basename:
                simple_filename_lower = f"{basename.split('/')[-1]}_{language}.prompt".lower()
                matching_modules = [
                    module for module in modules
                    if isinstance(module, dict)
                    and str(module.get("filename") or "").lower() == simple_filename_lower
                ]
                safe_matches = [
                    module for module in matching_modules
                    if _module_filepath_matches_basename(
                        module.get("filepath"), basename, context_name=context_name,
                        pddrc_anchor=architecture_path.parent,
                    )
                    and _borrow_ownership_ok(module)
                ]
                if len(safe_matches) == 1:
                    return safe_matches[0].get("filepath"), safe_matches[0].get("filename")

            # Canonical architecture normalization derives filename from filepath.
            # Consumer repositories may still keep a prompt in a context-specific
            # prompts_dir, so the prompt path and normalized architecture filename
            # need not share directory segments. A unique, language-compatible
            # filepath identity is still safe to use.
            expected_extension = get_extension(language).lower()
            relative_basename = _relative_basename_for_context(basename, context_name, pddrc_anchor)
            target_leaf = PurePosixPath(relative_basename).name
            filepath_match = _unique_match([
                module
                for module in modules
                if isinstance(module, dict)
                and not extract_module_from_include(
                    PurePosixPath(
                        str(module.get("filename", "")).replace("\\", "/")
                    ).name
                )
                and isinstance(module.get("filepath"), str)
                and PurePosixPath(module["filepath"]).stem.lower() == target_leaf.lower()
                and (
                    not expected_extension
                    or PurePosixPath(module["filepath"]).suffix.lower()
                    == f".{expected_extension}"
                )
                and _aligns(module)
                and _borrow_ownership_ok(module)
            ])
            if filepath_match[0]:
                return filepath_match

        return None, None

    except (FileNotFoundError, json.JSONDecodeError, TypeError):
        return None, None


def _contained_architecture_code_path(
    project_root: Path,
    architecture_filepath: str,
) -> Optional[Path]:
    """Resolve a safe repository-relative architecture output path.

    Architecture metadata can be generated or hand-edited. It must never turn a
    sync operation into an arbitrary filesystem write. Architecture filepaths use
    POSIX separators by contract; absolute paths, parent traversal, backslashes,
    and symlink-assisted escapes are rejected so callers can fall back to the
    repository's configured output template.
    """
    if not isinstance(architecture_filepath, str):
        return None

    if architecture_filepath != architecture_filepath.strip():
        return None
    raw = architecture_filepath
    if not raw or _contains_disallowed_path_text(raw):
        return None
    # Drive-qualified output metadata (e.g. "D:/x.py", "D:x.py") is POSIX-relative
    # but escapes the project root when joined on Windows. Reject it so callers fall
    # back to the configured output template.
    if PureWindowsPath(raw).drive:
        return None

    try:
        relative = PurePosixPath(raw)
        if (
            not relative.parts
            or relative.as_posix() != raw
            or relative.is_absolute()
            or ".." in relative.parts
            or any(
                _unsafe_portable_path_component(part)
                for part in relative.parts
            )
        ):
            return None

        resolved_root = project_root.resolve(strict=False)
        candidate = resolved_root.joinpath(*relative.parts).resolve(strict=False)
        candidate.relative_to(resolved_root)
    except (OSError, RuntimeError, ValueError):
        return None
    return candidate


def _governing_output_root(config_anchor: Path) -> Tuple[Path, bool]:
    """The single trusted root that every resolved output must live under.

    Authority comes from PROVENANCE, never from the process CWD: the governing
    ``.pddrc`` directory, else the ``architecture.json`` directory. Outputs are
    always anchored under this root — a parent/sibling-CWD run does not widen the
    boundary. Only when neither config exists (a loose, unconfigured tree) does the
    root fall back to ``config_anchor`` (which is CWD in that case). Returns
    ``(root, has_project_config)``.
    """
    pddrc = _find_pddrc_file(config_anchor)
    if pddrc is not None:
        return pddrc.parent.resolve(strict=False), True
    arch = _find_architecture_json(config_anchor)
    if arch is not None:
        return arch.parent.resolve(strict=False), True
    return config_anchor.resolve(strict=False), False


def _reanchor_output_to_root(
    path: Any, governing_root: Path, has_project_config: bool
) -> Path:
    """Anchor an output path under the governing project root.

    A relative path joins the root. An absolute path already inside the root is
    left unchanged. An absolute path that a branch anchored at the process CWD
    (outside the governing root) is relativised against CWD and re-anchored under
    the root, so a parent/sibling-CWD run still writes UNDER the project instead of
    beside it. A path that is outside both the root and CWD is left as-is for the
    containment check to reject.
    """
    p = Path(path)
    root_resolved = governing_root.resolve(strict=False)
    try:
        cwd = Path.cwd().resolve(strict=False)
    except (OSError, RuntimeError, ValueError):
        cwd = root_resolved
    if not p.is_absolute():
        # Relative paths resolve against the CWD. When the CWD IS the governing
        # root they already land under it — keep them relative to preserve the
        # legacy return contract. From a parent/sibling CWD, re-anchor them under
        # the governing root so the write still lands under the project.
        if cwd == root_resolved:
            return p
        return governing_root / p
    try:
        p_resolved = p.resolve(strict=False)
    except (OSError, RuntimeError, ValueError):
        return p
    try:
        p_resolved.relative_to(root_resolved)
        return p  # already under the governing root
    except ValueError:
        pass
    if has_project_config and cwd != root_resolved:
        # An absolute output a branch anchored at the CWD (outside the governing
        # root) is re-anchored under the project.
        try:
            return governing_root / p_resolved.relative_to(cwd)
        except (OSError, RuntimeError, ValueError):
            pass
    return p


def _output_path_within_root(path: Any, project_root: Path) -> bool:
    """Whether ``path`` resolves (symlinks followed) inside ``project_root`` AND
    every component below the root is portable/canonical (R9/R10 parity).

    Containment alone is not enough: a non-portable component (Windows device
    name, NTFS ADS colon, drive marker, control char) can survive ``resolve()``
    and stay physically inside the root on POSIX. Rejecting such components here
    catches values that reached a sink WITHOUT passing the raw ``.pddrc`` gate
    (e.g. a nearer descendant ``.pddrc`` selected by ``construct_paths``).
    """
    try:
        resolved = Path(path).resolve(strict=False)
        root_resolved = project_root.resolve(strict=False)
        relative = resolved.relative_to(root_resolved)
    except (OSError, RuntimeError, ValueError):
        return False
    return not any(
        _unsafe_portable_path_component(part) or _contains_disallowed_path_text(part)
        for part in relative.parts
    )


def _ensure_output_within_root(
    path: Any, project_root: Path, artifact: str
) -> Any:
    """Return ``path`` when contained + portable under the root; else fail closed."""
    if not _output_path_within_root(path, project_root):
        raise UnsafeOutputPathError(path, project_root, artifact)
    return path


def _configured_output_escapes_root(raw: Any, project_root: Path) -> bool:
    """Whether a RAW absolute ``.pddrc`` output value points outside ``project_root``.

    Only ABSOLUTE (or Windows-drive) configured values are checked here: an
    explicit away-pointing absolute destination must fail closed rather than be
    silently re-anchored under the project. Relative values are left to the
    provenance-based re-anchoring + containment path (they cannot be told apart
    from a legitimate CWD expansion once resolved).
    """
    if not isinstance(raw, str) or not raw:
        return False
    if not (PurePosixPath(raw).is_absolute() or PureWindowsPath(raw).drive):
        return False
    try:
        Path(raw).resolve(strict=False).relative_to(project_root.resolve(strict=False))
        return False
    except (OSError, RuntimeError, ValueError):
        return True


def _configured_output_string_is_unsafe(raw: Any) -> bool:
    """Whether a ``.pddrc`` output path/dir/template value is unsafe.

    Applies the same portability/traversal validation the architecture code
    filepath gets (R7/R9/R10), but on the RAW configured string BEFORE it is
    joined and resolved — so it is independent of the process CWD and catches
    parent traversal (``..``) that a later ``Path.resolve()`` would normalize
    away. Rejects backslashes, control/format/line-separator characters, Windows
    drive markers, parent traversal, and non-portable components (Windows-invalid
    characters, reserved device names, NTFS ADS colons, trailing dot/space).
    ``{placeholder}`` template segments and a trailing slash (directory form) are
    permitted. A None/empty value is ABSENT (a default applies), but any OTHER
    present non-string value (int, list, mapping, bool) is malformed and unsafe —
    it would otherwise slip past this string validation and later raise inside
    ``str``-only path handling, degrading to an uncontained convention fallback.
    """
    if raw is None or raw == "":
        return False
    if not isinstance(raw, str):
        return True
    if "\\" in raw or _contains_disallowed_path_text(raw):
        return True
    if PureWindowsPath(raw).drive:
        return True
    for part in PurePosixPath(raw).parts:
        if part in ("/", ""):
            continue
        if part == "..":
            return True
        if part.startswith("{") and part.endswith("}"):
            continue  # whole-segment template placeholder, e.g. {category}
        if _unsafe_portable_path_component(part):
            return True
    return False


def _reject_unsafe_output_config(
    project_root: Path,
    artifact: str,
    *raw_values: Any,
    reject_absolute: bool = False,
) -> None:
    """Fail closed on any unsafe ``.pddrc`` output directory/template value.

    ``reject_absolute`` is set for ``outputs.<artifact>.path`` TEMPLATES: those go
    through template normalization, which strips a POSIX leading slash and would
    re-anchor an absolute in-project template into a doubled path — so an absolute
    template is rejected rather than silently mangled. Directory values
    (generate/example/test_output_path) still accept an absolute in-project path.
    """
    for raw in raw_values:
        if _configured_output_string_is_unsafe(raw) or _configured_output_escapes_root(
            raw, project_root
        ):
            raise UnsafeOutputPathError(raw, project_root, artifact)
        if (
            reject_absolute
            and isinstance(raw, str)
            and (PurePosixPath(raw).is_absolute() or PureWindowsPath(raw).drive)
        ):
            raise UnsafeOutputPathError(raw, project_root, artifact)


def _reject_unsafe_outputs_templates(
    outputs_config: Any, project_root: Path
) -> None:
    """Fail closed on a malformed or unsafe ``outputs`` mapping.

    The supported shape is ``outputs: {<artifact>: {path: <str>}}``. A present but
    non-mapping ``outputs`` value, or an artifact entry that is present but not a
    mapping (e.g. ``code: "src/{name}.py"`` written without the ``path:`` key), is
    malformed — it would be silently ignored and degrade to a convention path — so
    it fails closed. Absolute template paths are rejected (see ``reject_absolute``).
    """
    if outputs_config is None:
        return
    if not isinstance(outputs_config, dict):
        raise UnsafeOutputPathError(outputs_config, project_root, "outputs")
    for artifact, entry in outputs_config.items():
        if entry is None:
            continue
        if not isinstance(entry, dict):
            raise UnsafeOutputPathError(entry, project_root, str(artifact))
        # A PRESENT artifact entry must carry a non-empty string `path`. A pathless
        # (e.g. `code: {}`) or empty/non-string path is malformed: the mere presence
        # of the key suppresses the configured legacy fallback downstream, silently
        # degrading to a convention path. Fail closed instead.
        _path = entry.get("path")
        if not isinstance(_path, str) or not _path:
            raise UnsafeOutputPathError(_path, project_root, str(artifact))
        _reject_unsafe_output_config(
            project_root, str(artifact), _path, reject_absolute=True
        )


def _reject_unsafe_pddrc_output_config(config_anchor: Path) -> None:
    """Fail closed EARLY on any unsafe ``.pddrc`` output destination.

    Validated once, before any branch-specific ``.pddrc`` load — whose
    ``except ValueError`` / ``except Exception`` config-tolerance would otherwise
    swallow the raised :class:`UnsafeOutputPathError` (a ``ValueError`` subclass)
    and silently continue with the unsafe destination. This runs inside the
    function's top-level ``try`` whose ``except AmbiguousModuleError: raise`` lets
    the error propagate. Every context's output settings are checked so an unsafe
    destination fails closed regardless of which context the resolution selects.
    A malformed ``.pddrc`` is left to the existing per-branch handling.
    """
    pddrc_path = _find_pddrc_file(config_anchor)
    if pddrc_path is None:
        return
    try:
        config = _load_pddrc_config(pddrc_path)
    except (ValueError, OSError):
        return
    if not isinstance(config, dict):
        return
    contexts = config.get("contexts", {})
    if not isinstance(contexts, dict):
        return
    project_root = pddrc_path.parent.resolve(strict=False)
    for context in contexts.values():
        if not isinstance(context, dict):
            continue
        defaults = context.get("defaults", {})
        if not isinstance(defaults, dict):
            continue
        _reject_unsafe_output_config(
            project_root, "code", defaults.get("generate_output_path")
        )
        _reject_unsafe_output_config(
            project_root, "example", defaults.get("example_output_path")
        )
        _reject_unsafe_output_config(
            project_root, "test", defaults.get("test_output_path")
        )
        _reject_unsafe_outputs_templates(defaults.get("outputs"), project_root)
        # A present but non-string `prompts_dir` is malformed: it would reach the
        # string-only context-prefix extraction, raise, and degrade to a wrong
        # convention path. Fail closed instead (None/empty means "unset").
        _prompts_dir_cfg = defaults.get("prompts_dir")
        if _prompts_dir_cfg is not None and not isinstance(_prompts_dir_cfg, str):
            raise UnsafeOutputPathError(_prompts_dir_cfg, project_root, "prompts_dir")


def _architecture_module_choices(
    architecture_path: Path,
    basename: str,
    language: str,
    modules: Any = _ARCH_MODULES_UNSET,
    context_name: Optional[str] = None,
) -> List[str]:
    """Return the distinct canonical output files a BARE basename maps to.

    Issue #1677: used to detect ambiguity before resolving/generating. A return
    value with two or more entries means ``basename`` is ambiguous for ``language``
    (it would otherwise be resolved by silent first-match-wins or a ``.pddrc``
    default). Path-qualified basenames (containing ``/``) are already disambiguated
    by their directory, so this returns ``[]`` for them.

    Matching is by prompt FILENAME leaf (``<basename>_<language>.prompt``, case
    insensitive) — exactly how :func:`_get_filepath_from_architecture` resolves a
    bare basename — NEVER by the filepath stem. The filename is compared by its leaf
    segment so directory-qualified architecture filenames (e.g.
    ``app/login/page_TypeScriptReact.prompt``, produced by
    ``normalize_architecture_filenames``) are matched too. This is deliberate: a
    different module whose code file merely happens to be named ``page.tsx`` (e.g. a
    ``home`` route with ``filepath`` ``src/home/page.tsx`` and filename
    ``home_*.prompt``) must not be treated as a match for ``page``, otherwise a
    uniquely-named module would be falsely reported as ambiguous. The
    language-specific filename also means a module that exists in two languages
    (``foo.py`` + ``foo.ts``) is not flagged for a single-language query.

    A single ``architecture.json`` lists every filepath relative to one root, so the
    distinct targets are simply the deduplicated matched filepaths — two filepaths
    that differ at all (e.g. ``src/page.tsx`` vs ``frontend/src/page.tsx``) are
    genuinely different modules and remain distinct. (The agentic *combined*
    multi-architecture view resolves filepaths against each source architecture's
    directory before comparing; see ``agentic_sync._architecture_outputs_by_basename``.)
    """
    if modules is _ARCH_MODULES_UNSET:
        try:
            with open(architecture_path, "r", encoding="utf-8") as handle:
                modules = extract_modules(json.load(handle))
        except (FileNotFoundError, json.JSONDecodeError, TypeError, OSError):
            return []

    if not modules:
        return []

    if "/" in basename:
        # A path-qualified basename is NOT automatically unambiguous: because a qualified
        # basename matches by path-SUFFIX, more than one distinct valid output can align
        # (e.g. `app/login/page` matches both `app/login/page.tsx` and
        # `src/app/login/page.tsx`). Collect the distinct valid suffix-aligned outputs so
        # the caller raises AmbiguousModuleError instead of resolving by architecture row
        # order. A single (or zero) match keeps the canonical resolution unchanged.
        lang_ext_q = get_extension(language).lower()
        qualified: set = set()
        for module in modules:
            if not isinstance(module, dict):
                continue
            # Exclude rows with an unsafe architecture FILENAME (as the bare branch and
            # resolution do), so an invalid row cannot inflate the count and falsely block
            # a valid mapping.
            filename_value_q = module.get("filename")
            if (
                isinstance(filename_value_q, str)
                and filename_value_q != ""
                and _safe_architecture_prompt_filename(filename_value_q) is None
            ):
                # A non-empty STRING filename that fails validation (incl. whitespace-only)
                # is unsafe/ineligible in selection too — skip it so it cannot inflate the
                # count. An EMPTY string and null/non-string stay filepath-stem-eligible.
                continue
            # Mirror selection eligibility: a row whose PROMPT filename names a DIFFERENT
            # module (its leaf is a recognized prompt filename but not this module's) is not
            # a candidate for this basename — only a filename that names this module, or a
            # null/non-prompt filename (filepath-stem eligible), counts. Otherwise a
            # coincidentally suffix-aligned foreign row raises a false AmbiguousModuleError
            # before selection uniquely resolves the named row.
            filename_leaf_q = PurePosixPath(
                str(filename_value_q or "").replace("\\", "/")
            ).name.lower()
            target_prompt_leaf = f"{basename.split('/')[-1].lower()}_{language.lower()}.prompt"
            if (
                filename_leaf_q != target_prompt_leaf
                and filename_value_q
                and extract_module_from_include(filename_leaf_q)
            ):
                continue
            filepath_value = module.get("filepath")
            if not isinstance(filepath_value, str) or not filepath_value.strip():
                continue
            # Cheap pure-string checks FIRST — use the SAME context-relative basename and
            # anchor as final resolution, so a context-prefixed qualified basename (stripped
            # during resolution) is counted consistently instead of evading detection under
            # the raw prefix — then pay the filesystem containment resolve only for the rows
            # that already match, not every registry row.
            if not _module_filepath_matches_basename(
                filepath_value, basename,
                context_name=context_name, pddrc_anchor=architecture_path.parent,
            ):
                continue
            if lang_ext_q and PurePosixPath(filepath_value).suffix.lstrip(".").lower() != lang_ext_q:
                continue
            # Validate the RAW filepath (not a stripped copy): a trailing-space or
            # otherwise noncanonical value that resolution rejects must not be counted.
            if _contained_architecture_code_path(architecture_path.parent, filepath_value) is None:
                continue
            qualified.add(PurePosixPath(filepath_value).as_posix())
        return sorted(qualified)

    target_filename = f"{basename}_{language}.prompt".lower()
    lang_ext = get_extension(language).lower()
    distinct: set = set()
    for module in modules:
        if not isinstance(module, dict):
            continue
        filepath_value = module.get("filepath")
        # A non-string filepath is malformed metadata, not a real output: skip it so
        # it cannot be stringified (e.g. 123 -> "123") into a bogus distinct target
        # that falsely raises AmbiguousModuleError and blocks a valid mapping.
        if not isinstance(filepath_value, str):
            continue
        filepath = filepath_value.strip()
        if not filepath:
            continue
        filename_value = module.get("filename")
        # A non-empty STRING filename that fails validation (unsafe path, OR whitespace-only,
        # which selection also treats as ineligible) is excluded from ambiguity counting. An
        # EMPTY string and null/non-string are left to the filepath-stem branch (the module
        # is filepath-owned). Cheap string check before the filesystem containment resolve.
        if (
            isinstance(filename_value, str)
            and filename_value != ""
            and _safe_architecture_prompt_filename(filename_value) is None
        ):
            continue
        filename = filename_value if isinstance(filename_value, str) else ""
        if filename.endswith("_LLM.prompt"):
            continue
        leaf = Path(filename).name
        matched = leaf.lower() == target_filename
        if not matched and not extract_module_from_include(leaf):
            # Non-prompt architecture filename (e.g. `GitHubAppCTA.tsx`): the module
            # is identified by its filepath stem instead. Gate on the language
            # extension so a same-stem file in another language is not conflated.
            suffix = Path(filepath).suffix.lstrip(".").lower()
            matched = bool(
                Path(filepath).stem.lower() == basename.lower()
                and lang_ext
                and suffix == lang_ext
            )
        if not matched:
            continue
        # Only NOW — for the handful of filename/stem matches, not every module — pay
        # the filesystem containment resolution. An unsafe OUTPUT path (absolute, ``..``,
        # backslash, Windows drive, symlink escape) is rejected before generation, so it
        # must not count toward ambiguity: otherwise a valid ``foo -> src/foo.py`` plus a
        # same-filename ``foo -> ../../outside/foo.py`` read as two targets and raise
        # AmbiguousModuleError, blocking the valid module.
        # Validate the RAW filepath so a trailing-space / noncanonical value (which
        # resolution rejects) is not canonicalized by the earlier strip and counted.
        if _contained_architecture_code_path(architecture_path.parent, filepath_value) is None:
            continue
        distinct.add(Path(filepath).as_posix())

    return sorted(distinct)


@dataclass
class Fingerprint:
    """Represents the last known good state of a PDD unit."""
    pdd_version: str
    timestamp: str  # ISO 8601 format
    command: str    # e.g., "generate", "fix"
    prompt_hash: Optional[str]
    code_hash: Optional[str]
    example_hash: Optional[str]
    test_hash: Optional[str]  # Keep for backward compat (primary test file)
    test_files: Optional[Dict[str, str]] = None  # Bug #156: {"test_foo.py": "hash1", ...}
    include_deps: Optional[Dict[str, str]] = None  # Issue #522: {"path": "hash", ...}


@dataclass
class RunReport:
    """Represents the results from the last test run."""
    timestamp: str
    exit_code: int
    tests_passed: int
    tests_failed: int
    coverage: float
    test_hash: Optional[str] = None  # Hash of test file when tests were run (for staleness detection)
    test_files: Optional[Dict[str, str]] = None  # Bug #156: {"test_foo.py": "hash1", ...}


@dataclass
class SyncDecision:
    """Represents a decision about what PDD operation to run next."""
    operation: str  # 'auto-deps', 'generate', 'example', 'crash', 'verify', 'test', 'fix', 'update', 'nothing', 'all_synced', 'error', 'fail_and_request_manual_merge'
    reason: str  # A human-readable explanation for the decision
    confidence: float = 1.0  # Confidence level in the decision, 0.0 to 1.0, default 1.0 for deterministic decisions
    estimated_cost: float = 0.0  # Estimated cost for the operation in dollars, default 0.0
    details: Optional[Dict[str, Any]] = None  # Extra context for logging and debugging, default None
    prerequisites: Optional[List[str]] = None  # List of operations that should be completed first, default None


COMPLETED_VERIFY_COMMANDS = {'verify', 'test', 'fix', 'update'}
COMPLETED_TEST_COMMANDS = {'test', 'fix', 'update'}


class SyncLock:
    """Context manager for handling file-descriptor based locking."""
    
    def __init__(self, basename: str, language: str):
        self.basename = basename
        self.language = language
        locks_root = get_locks_dir()
        lock_file = locks_root / (
            f"{_safe_lock_component(basename)}_"
            f"{_safe_lock_component(str(language).lower())}.lock"
        )
        # Defense in depth: the sanitized components carry no separators, so the
        # lock file can never resolve outside the locks directory. Assert it so a
        # future change to the naming scheme fails loudly instead of silently
        # letting a lock escape onto an arbitrary out-of-tree path.
        resolved_root = locks_root.resolve(strict=False)
        if resolved_root not in lock_file.resolve(strict=False).parents:
            raise UnsafeOutputPathError(lock_file, resolved_root, "lock")
        self.lock_file = lock_file
        self.fd = None
        self.current_pid = os.getpid()
    
    def __enter__(self):
        self.acquire()
        return self
    
    def __exit__(self, exc_type, exc_val, exc_tb):
        self.release()
    
    def acquire(self):
        """Acquire the lock, handling stale locks and re-entrancy."""
        # Ensure lock directory exists
        self.lock_file.parent.mkdir(parents=True, exist_ok=True)
        
        try:
            # Check if lock file exists
            if self.lock_file.exists():
                try:
                    # Read PID from lock file
                    stored_pid = int(self.lock_file.read_text().strip())
                    
                    # Check if this is the same process (re-entrancy)
                    if stored_pid == self.current_pid:
                        return
                    
                    # Check if the process is still running
                    if psutil.pid_exists(stored_pid):
                        raise TimeoutError(f"Lock held by running process {stored_pid}")
                    
                    # Stale lock - remove it
                    self.lock_file.unlink(missing_ok=True)
                    
                except (ValueError, FileNotFoundError):
                    # Invalid lock file - remove it
                    self.lock_file.unlink(missing_ok=True)
            
            # Create lock file and acquire file descriptor lock
            self.lock_file.touch()
            self.fd = open(self.lock_file, 'w')
            
            if HAS_FCNTL:
                # POSIX systems
                fcntl.flock(self.fd.fileno(), fcntl.LOCK_EX | fcntl.LOCK_NB)
            elif HAS_MSVCRT:
                # Windows systems
                msvcrt.locking(self.fd.fileno(), msvcrt.LK_NBLCK, 1)
            
            # Write current PID to lock file
            self.fd.write(str(self.current_pid))
            self.fd.flush()
            
        except (IOError, OSError) as e:
            # Ensure file descriptor is closed and lock file removed on ANY failure
            try:
                if self.fd:
                    try:
                        self.fd.close()
                    finally:
                        self.fd = None
            finally:
                try:
                    self.lock_file.unlink(missing_ok=True)
                except Exception:
                    pass
            # Re-raise so caller receives the original exception (tests expect RuntimeError etc.)
            raise
    
    def release(self):
        """Release the lock and clean up."""
        if self.fd:
            try:
                if HAS_FCNTL:
                    fcntl.flock(self.fd.fileno(), fcntl.LOCK_UN)
                elif HAS_MSVCRT:
                    msvcrt.locking(self.fd.fileno(), msvcrt.LK_UNLCK, 1)
                
                self.fd.close()
                self.fd = None
                
                # Remove lock file
                self.lock_file.unlink(missing_ok=True)
                
            except (IOError, OSError):
                # Best effort cleanup
                pass


def get_extension(language: str) -> str:
    """Get file extension (without a leading dot) for a programming language.

    Resolves through the shared, PDD_PATH-independent
    ``pdd.language_extensions.bundled_extension`` reader of the canonical
    language_format.csv, so the extensions sync *expects* match the ones
    generation *writes* (issue #551). Falls back to a hard-coded subset for
    languages absent from the CSV, then to the raw lower-cased language name.
    """
    from pdd.language_extensions import bundled_extension

    ext = bundled_extension(language)
    if ext is not None:
        return ext

    # CSV unreadable or language absent from it: defer to the SAME hard-coded map
    # generation uses (construct_paths.BUILTIN_EXT_MAP), so sync and generation
    # share one offline fallback and cannot diverge even when the bundled CSV
    # can't be read (issue #551). Returned without a leading dot per this
    # function's contract; BUILTIN_EXT_MAP stores values with the dot ('' for
    # Makefile), and unknown languages fall through to the raw language name.
    from pdd.construct_paths import BUILTIN_EXT_MAP

    lang_lower = language.lower()
    return BUILTIN_EXT_MAP.get(lang_lower, lang_lower).lstrip('.')


def _dot(extension: str) -> str:
    """Return a dotted suffix (".ext") for *extension*, or "" when empty.

    Languages like Makefile have no canonical extension (an empty cell in
    language_format.csv), so ``get_extension`` can return ''. Appending
    ".{extension}" unconditionally would produce a malformed trailing-dot
    path such as 'tests/test_Build.'; this keeps it clean ('tests/test_Build')
    and matches how the write side (construct_paths.BUILTIN_EXT_MAP) treats
    extensionless languages.
    """
    return f".{extension}" if extension else ""


def _resolve_prompts_root(prompts_dir: str) -> Path:
    """
    Resolve prompts root relative to the .pddrc location when available.

    Note: This function previously stripped subdirectories after "prompts" which was
    incorrect for context-specific prompts_dir values. Fixed in Issue #253/237.
    """
    prompts_root = Path(prompts_dir)
    pddrc_path = _find_pddrc_file()
    if pddrc_path and not prompts_root.is_absolute():
        prompts_root = pddrc_path.parent / prompts_root

    return prompts_root


def _relative_basename_for_context(
    basename: str,
    context_name: Optional[str],
    pddrc_anchor: Optional[Path] = None,
) -> str:
    """Strip context-specific prefixes from basename when possible.

    ``pddrc_anchor`` anchors the ``.pddrc`` lookup at the project instead of the
    process CWD; without it a resolution driven from a parent/sibling directory with
    an absolute prompts root cannot strip the context prefix, so a path-qualified
    basename fails to align with its canonical architecture filepath and silently
    falls back to the default output path.
    """
    if not context_name:
        return basename

    pddrc_path = _find_pddrc_file(pddrc_anchor)
    if not pddrc_path:
        return basename

    try:
        config = _load_pddrc_config(pddrc_path)
    except ValueError:
        return basename

    contexts = config.get("contexts", {})
    context_config = contexts.get(context_name, {})
    defaults = context_config.get("defaults", {})

    matches = []

    prompts_dir = defaults.get("prompts_dir", "")
    if prompts_dir:
        prefix = _extract_prefix_from_prompts_dir(prompts_dir)

        if prefix and (basename == prefix or basename.startswith(prefix + "/")):
            relative = basename[len(prefix) + 1 :] if basename != prefix else basename.split("/")[-1]
            matches.append((len(prefix), relative))

    for pattern in context_config.get("paths", []):
        pattern_base = pattern.rstrip("/**").rstrip("/*")
        if fnmatch.fnmatch(basename, pattern) or \
           basename.startswith(pattern_base + "/") or \
           basename == pattern_base:
            relative = _get_relative_basename(basename, pattern)
            matches.append((len(pattern_base), relative))

    if not matches:
        return basename

    matches.sort(key=lambda item: item[0], reverse=True)
    return matches[0][1]


def _generate_paths_from_templates(
    basename: str,
    language: str,
    extension: str,
    outputs_config: Dict[str, Any],
    prompt_path: str
) -> Dict[str, Path]:
    """
    Generate file paths from template configuration.

    This function is used by Issue #237 to support extensible output path patterns
    for different project layouts (Next.js, Vue, Python backend, etc.).

    Args:
        basename: The relative basename (e.g., 'marketplace/AssetCard' or 'credit_helpers')
        language: The full language name (e.g., 'python', 'typescript')
        extension: The file extension (e.g., 'py', 'tsx')
        outputs_config: The 'outputs' section from .pddrc context config
        prompt_path: The prompt file path to use as fallback

    Returns:
        Dictionary mapping file types ('prompt', 'code', 'test', etc.) to Path objects
    """
    import logging
    logger = logging.getLogger(__name__)

    # Extract name parts for template context
    parts = basename.split('/')
    name = parts[-1] if parts else basename
    category = '/'.join(parts[:-1]) if len(parts) > 1 else ''

    # Issue #237 fix: If category is empty but we have an actual prompt_path,
    # try to derive the category from the prompt path by comparing with template
    if not category and prompt_path and Path(prompt_path).exists():
        prompt_template = outputs_config.get('prompt', {}).get('path', '')
        if prompt_template and '{category}' in prompt_template:
            # Extract category from actual prompt path
            # Template: prompts/frontend/{category}/{name}_{language}.prompt
            # Actual:   prompts/frontend/app/page_TypescriptReact.prompt
            # Category: app
            prompt_path_obj = Path(prompt_path)
            prompt_parts = prompt_path_obj.parts

            # Find where the template's fixed prefix ends
            # E.g., "prompts/frontend/" -> look for index after "frontend"
            template_prefix = prompt_template.split('{category}')[0].rstrip('/')
            template_prefix_parts = Path(template_prefix).parts if template_prefix else ()

            # Find the matching index in the actual path
            if template_prefix_parts:
                for i, part in enumerate(prompt_parts):
                    if prompt_parts[i:i+len(template_prefix_parts)] == template_prefix_parts:
                        # Category starts after the prefix, ends before the filename
                        category_start = i + len(template_prefix_parts)
                        category_end = len(prompt_parts) - 1  # Exclude filename
                        if category_start < category_end:
                            category = '/'.join(prompt_parts[category_start:category_end])
                            logger.info(f"Derived category '{category}' from prompt path: {prompt_path}")
                        break

    # Build dir_prefix (for legacy template compatibility)
    dir_prefix = '/'.join(parts[:-1]) + '/' if len(parts) > 1 else ''
    if category and not dir_prefix:
        dir_prefix = category + '/'

    # Build template context
    template_context = {
        'name': name,
        'category': category,
        'dir_prefix': dir_prefix,
        'ext': extension,
        'language': language,
    }

    logger.debug(f"Template context: {template_context}")

    result = {}

    # Expand templates for each output type
    for output_type, config in outputs_config.items():
        if isinstance(config, dict) and 'path' in config:
            template = config['path']
            expanded = expand_template(template, template_context)
            result[output_type] = Path(expanded)
            if output_type == 'prompt':
                from pdd.sync_main import _case_insensitive_prompt_lookup
                result[output_type] = _case_insensitive_prompt_lookup(result[output_type])
            logger.debug(f"Template {output_type}: {template} -> {expanded}")

    # Ensure prompt is always present (fallback to provided prompt_path)
    if 'prompt' not in result:
        result['prompt'] = Path(prompt_path)

    # Ensure code, example, and test paths are always present (fallback to defaults)
    # This maintains compatibility with sync workflow that expects these keys.
    # sync_orchestration.py accesses pdd_files['code'] directly (20+ places).
    if 'code' not in result:
        result['code'] = Path(f"{dir_prefix}{name}{_dot(extension)}")
    if 'example' not in result:
        result['example'] = Path(f"examples/{name}_example{_dot(extension)}")
    if 'test' not in result:
        result['test'] = Path(f"tests/test_{name}{_dot(extension)}")

    # Handle test_files for Bug #156 compatibility
    if 'test' in result:
        test_path = result['test']
        test_dir_path = test_path.parent
        test_stem = f"test_{glob.escape(name)}"
        if test_dir_path.exists():
            matching_test_files = sorted(test_dir_path.glob(f"{test_stem}*.{glob.escape(extension)}"))
        else:
            matching_test_files = [test_path] if test_path.exists() else []
        result['test_files'] = matching_test_files or [test_path]

    return result


def get_pdd_file_paths(basename: str, language: str, prompts_dir: str = "prompts", context_override: Optional[str] = None) -> Dict[str, Path]:
    """Returns a dictionary mapping file types to their expected Path objects.

    Issue #225: Now checks architecture.json for filepath field before falling
    back to .pddrc configuration. This allows complex directory structures
    defined in architecture.json to be respected by sync.

    Priority order for code path resolution:
    1. architecture.json filepath field (if present)
    2. .pddrc outputs config (template-based paths)
    3. .pddrc generate_output_path config
    4. Default naming conventions
    """
    import logging
    logger = logging.getLogger(__name__)

    try:
        # Use construct_paths to get configuration-aware paths
        if (
            not isinstance(prompts_dir, str)
            or not prompts_dir
            or prompts_dir != prompts_dir.strip()
            or _contains_disallowed_path_text(prompts_dir)
        ):
            raise UnsafePromptPathError(Path(str(prompts_dir)), Path.cwd())
        prompts_root = _resolve_prompts_root(prompts_dir)
        if _safe_architecture_prompt_filename(basename) is None:
            raise UnsafePromptPathError(
                Path(basename), prompts_root.resolve(strict=False)
            )
        if _safe_prompt_language(language) is None:
            raise UnsafePromptPathError(
                Path(str(language)), prompts_root.resolve(strict=False)
            )
        logger.info(
            "get_pdd_file_paths called: basename=%s, language=%s, prompts_dir=%r",
            basename,
            language,
            prompts_dir,
        )
        name = basename.split('/')[-1] if '/' in basename else basename

        # Anchor configuration lookups (architecture.json, .pddrc) at the resolved
        # prompts root so nested subprojects (e.g. extensions/<name>/prompts/) find
        # their own architecture.json/.pddrc rather than falling back to the
        # caller's CWD, which would honor configured output paths inconsistently.
        # Established BEFORE context/prefix resolution so those lookups are also
        # CWD-independent (parent-CWD runs must still detect the context and strip the
        # basename prefix instead of duplicating it in example/test templates).
        prompts_root_anchor = prompts_root if prompts_root.is_absolute() else prompts_root.resolve()

        # When an absolute custom prompt root lies OUTSIDE any project (searching up from it
        # finds neither architecture.json nor .pddrc), config/architecture discovery would
        # start from that external root and silently miss the caller's project. Anchor
        # config lookups at the project (CWD) instead in that case; a nested subproject
        # prompt root (which DOES find its own config up-tree) still anchors at itself.
        config_anchor = prompts_root_anchor
        if (
            _find_pddrc_file(prompts_root_anchor) is None
            and _find_architecture_json(prompts_root_anchor) is None
        ):
            config_anchor = Path.cwd()

        # The single trusted project root every returned output must live under.
        # Authority is from PROVENANCE (the governing .pddrc / architecture.json
        # directory), NEVER the process CWD — so a parent/sibling-CWD run cannot
        # widen the boundary and authorise a write beside the real project (R16).
        _governing_root, _has_project_config = _governing_output_root(config_anchor)

        # R16: reject unsafe .pddrc output destinations up front (CWD-independent,
        # on the raw configured value) so parent traversal, non-portable components
        # (device names, ADS colons, drive markers), or control characters fail
        # closed before a branch-local `except ValueError` can swallow the error.
        _reject_unsafe_pddrc_output_config(config_anchor)

        def _finalize_output_paths(paths: Dict[str, Path]) -> Dict[str, Path]:
            # Re-anchor CWD-relative/absolute outputs UNDER the governing root, then
            # fail closed if the result escapes it or carries a non-portable
            # component (R16). The prompt is held to the prompts root (R8): an
            # outputs.prompt.path template must not return a prompt outside it.
            for _artifact in ("code", "example", "test"):
                _candidate = paths.get(_artifact)
                if _candidate is not None:
                    _reanchored = _reanchor_output_to_root(
                        _candidate, _governing_root, _has_project_config
                    )
                    paths[_artifact] = _reanchored
                    _ensure_output_within_root(
                        _reanchored, _governing_root, _artifact
                    )
            _test_files = paths.get("test_files")
            if isinstance(_test_files, list):
                # test_files are DISCOVERED (globbed) siblings handed to the test
                # runner. Re-anchor them, then DROP any entry that (via symlink or a
                # nearer config) resolves outside the governing root or carries a
                # non-portable component, so an out-of-project file is never executed.
                _contained_tfs = []
                for _tf in _test_files:
                    if isinstance(_tf, Path):
                        _tf = _reanchor_output_to_root(
                            _tf, _governing_root, _has_project_config
                        )
                        if not _output_path_within_root(_tf, _governing_root):
                            continue
                    _contained_tfs.append(_tf)
                _primary_test = paths.get("test")
                paths["test_files"] = _contained_tfs or (
                    [_primary_test] if _primary_test is not None else _test_files
                )
            _prompt = paths.get("prompt")
            if _prompt is not None:
                # A relative outputs.prompt.path (Issue #237, e.g. `custom/prompts/`)
                # is project-relative, not CWD-relative: anchor it under the
                # governing root the same way outputs are, so a parent/sibling-CWD
                # run still resolves it under the project instead of beside it.
                _prompt = _reanchor_output_to_root(
                    _prompt, _governing_root, _has_project_config
                )
                paths["prompt"] = _prompt
                # A nearer descendant .pddrc (governing the resolved prompt's own
                # subtree) may carry output values the up-front gate at config_anchor
                # never saw; validate its RAW values too so a normalized-away `..` or
                # a non-portable/non-string field fails closed (R16).
                _reject_unsafe_pddrc_output_config(Path(_prompt).parent)
                # R8: the returned prompt must not escape the project — an
                # outputs.prompt.path template must not hand back a FOREIGN prompt a
                # later `update` would overwrite. It is safe when it resolves inside
                # the prompts root OR anywhere inside the governing project (Issue
                # #237 lets outputs.prompt.path point at a custom in-project prompts
                # location such as `custom/prompts/`, which is legitimate); only a
                # path outside both is rejected. Resolve so a trusted in-root symlink
                # alias (prompts -> pdd/prompts) is preserved.
                try:
                    _prompt_resolved = Path(_prompt).resolve(strict=False)
                except (OSError, RuntimeError, ValueError):
                    raise UnsafePromptPathError(Path(_prompt), prompts_root_anchor)
                _prompt_ok = False
                for _root in (prompts_root_anchor, _governing_root):
                    try:
                        _prompt_resolved.relative_to(_root.resolve(strict=False))
                        _prompt_ok = True
                        break
                    except (OSError, RuntimeError, ValueError):
                        continue
                if not _prompt_ok:
                    raise UnsafePromptPathError(Path(_prompt), prompts_root_anchor)
            return paths

        resolved_context_name = _resolve_context_name_for_basename(
            basename, context_override, pddrc_anchor=config_anchor
        )
        construct_paths_basename = _relative_basename_for_context(
            basename, resolved_context_name, config_anchor
        )

        # Issue #225: Check architecture.json for filepath FIRST
        arch_path = _find_architecture_json(config_anchor)
        # Parse the architecture ONCE and thread this immutable snapshot through
        # ambiguity detection, prompt discovery, and code-path selection. Reading it
        # separately per phase lets an atomic rewrite of architecture.json between
        # phases pair a prompt from the old registry with a code target from the new
        # one (torn prompt/code pair); one snapshot also avoids the redundant parse.
        arch_modules: Any = _ARCH_MODULES_UNSET
        if arch_path:
            try:
                with open(arch_path, "r", encoding="utf-8") as _arch_handle:
                    _arch_data = json.load(_arch_handle)
            except FileNotFoundError:
                # Raced away between discovery and open — treat as no registry.
                _arch_data = _ARCH_MODULES_UNSET
                arch_modules = None
            except (json.JSONDecodeError, ValueError, TypeError, OSError) as _arch_err:
                # Present but unreadable/malformed: fail closed rather than downgrade to
                # an empty registry and resolve at convention fallback paths.
                raise MalformedArchitectureError(arch_path, _arch_err) from _arch_err
            else:
                # A present architecture.json must be a SUPPORTED shape: a bare module
                # list or an object. A dict MAY omit ``modules`` (a legitimately empty
                # registry), but a non-list ``modules`` value or a top-level scalar is
                # malformed schema — fail closed instead of silently treating valid JSON
                # of the wrong shape as an empty registry and resolving at fallback paths.
                _valid_shape = isinstance(_arch_data, list) or (
                    isinstance(_arch_data, dict)
                    and (
                        "modules" not in _arch_data
                        or isinstance(_arch_data.get("modules"), list)
                    )
                )
                if not _valid_shape:
                    raise MalformedArchitectureError(
                        arch_path,
                        f"unsupported architecture schema (top-level "
                        f"{type(_arch_data).__name__})",
                    )
                # Every module entry must be an object. extract_modules silently discards
                # non-object entries, which would let a corrupted registry fall through to
                # convention paths instead of failing closed.
                _module_list = (
                    _arch_data if isinstance(_arch_data, list)
                    else _arch_data.get("modules", [])
                )
                if any(not isinstance(_entry, dict) for _entry in _module_list):
                    raise MalformedArchitectureError(
                        arch_path, "modules list contains a non-object entry"
                    )
                arch_modules = extract_modules(_arch_data)
        prompt_ownership_roots: Tuple[Path, ...] = (prompts_root_anchor,)
        if arch_path:
            prompt_ownership_roots = _architecture_prompt_roots(
                prompts_root_anchor,
                arch_path,
            )

        # Issue #1677: fail fast on an ambiguous BARE basename BEFORE resolving a
        # prompt or falling back to a .pddrc default path. A short name such as
        # `page` (common in Next.js, where many files are `page.tsx`) that maps to
        # more than one architecture module must not be resolved by silent
        # first-match-wins or written to a generic `<generate_output_path>/page.tsx`.
        if arch_path:
            ambiguous_choices = _architecture_module_choices(
                arch_path, basename, language, modules=arch_modules,
                context_name=resolved_context_name,
            )
            if len(ambiguous_choices) > 1:
                raise AmbiguousModuleError(basename, language, ambiguous_choices)

        # Issue #1169: Use _find_prompt_file for authoritative prompt resolution.
        # This handles case-insensitive matching, nested subdirectories, and
        # architecture.json hints in a single code path.
        resolved_prompt = _find_prompt_file(basename, language, prompts_root, arch_path, context_override=context_override, arch_modules=arch_modules)
        if resolved_prompt:
            prompt_path = str(resolved_prompt)
        else:
            # File doesn't exist yet (new module being created) — construct expected path
            # Respect .pddrc context's prompts_dir prefix so new modules land in the
            # correct subdirectory (e.g., prompts/backend/utils/ not prompts/).
            prompt_filename = f"{name}_{language}.prompt"
            # Issue #1677: a path-qualified basename keeps its directory so a new
            # module lands at prompts/<dir>/<leaf> — never collapsing to the bare leaf,
            # which would otherwise re-resolve to an unrelated same-leaf module
            # elsewhere (e.g. `foo/page` picking up a root `page` prompt). Any leading
            # directory segments already present at the tail of prompts_root (a deep
            # prompts_dir passed by sync_main, or a context prefix) are stripped so they
            # are not duplicated.
            relative_basename = _relative_basename_for_context(
                basename, resolved_context_name, config_anchor
            )
            rel_dir_parts = Path(relative_basename).parts[:-1]
            root_parts = prompts_root.parts
            overlap = 0
            for k in range(min(len(root_parts), len(rel_dir_parts)), 0, -1):
                if root_parts[-k:] == rel_dir_parts[:k]:
                    overlap = k
                    break
            effective_dir_parts = rel_dir_parts[overlap:]
            if effective_dir_parts:
                prompt_path = str(prompts_root.joinpath(*effective_dir_parts, prompt_filename))
            else:
                prompt_path = str(prompts_root / prompt_filename)
            pddrc_path = _find_pddrc_file(config_anchor)
            if pddrc_path:
                try:
                    config = _load_pddrc_config(pddrc_path)
                    context_name = (
                        context_override
                        or resolved_context_name
                        or _detect_context(Path.cwd(), config, None)
                    )
                    context_config = config.get('contexts', {}).get(context_name or '', {})
                    prompts_dir_config = context_config.get('defaults', {}).get('prompts_dir', '')
                    if prompts_dir_config:
                        prefix = _context_prefix_for_prompts_root(
                            prompts_dir_config,
                            pddrc_path,
                            prompts_root_anchor,
                        )
                        prompts_root_ends_with_prefix = prefix and prompts_root.parts[-len(Path(prefix).parts):] == Path(prefix).parts
                        if prefix and not prompts_root_ends_with_prefix:
                            prompt_path = str(
                                prompts_root.joinpath(
                                    *Path(prefix).parts,
                                    *effective_dir_parts,
                                    prompt_filename,
                                )
                            )
                except ValueError:
                    pass

        logger.info(f"Checking prompt_path={prompt_path}, exists={Path(prompt_path).exists()}")

        # If architecture.json has a filepath, use it for code/test/example paths
        arch_filepath = None
        if arch_path:
            prompt_path_obj = Path(prompt_path)
            prompt_filename_for_lookup = Path(prompt_path).name
            try:
                prompt_filename_for_lookup = str(prompt_path_obj.resolve().relative_to(prompts_root.resolve())).replace(os.sep, "/")
            except ValueError:
                pass
            arch_filepath, _ = _get_filepath_from_architecture(
                arch_path,
                prompt_filename_for_lookup,
                basename=basename,
                language=language,
                prompt_path=prompt_path_obj,
                prompts_root=prompts_root,
                prompt_roots=prompt_ownership_roots,
                resolved_context_name=resolved_context_name,
                modules=arch_modules,
            )
            if arch_filepath:
                extension = get_extension(language)

                # Resolve filepath relative to architecture.json's directory (project root)
                project_root = arch_path.parent.resolve(strict=False)
                contained_code_path = _contained_architecture_code_path(project_root, arch_filepath)
                if contained_code_path is None:
                    logger.warning(
                        "Ignoring unsafe architecture.json filepath for %s: %r",
                        basename,
                        arch_filepath,
                    )
                    arch_filepath = None
                else:
                    # Containment (and territory ownership) is validated against the
                    # RESOLVED target, but the returned code path preserves
                    # architecture.json's authoritative validated filepath: an
                    # in-project symlink in the metadata is not silently rewritten to
                    # its physical target (which would lose filepath authority and
                    # re-point if the alias later moved).
                    arch_filepath = PurePosixPath(arch_filepath).as_posix()
                    logger.info(
                        "Found filepath in architecture.json: %r", arch_filepath
                    )
                    code_path = project_root / arch_filepath

            if arch_filepath:
                code_stem = code_path.stem

                # Get configured directories from .pddrc if available
                pddrc_path = _find_pddrc_file(config_anchor)
                example_dir = "examples/"
                test_dir = "tests/"
                generate_dir = ""
                outputs_config: Dict[str, Any] = {}
                if pddrc_path:
                    try:
                        config = _load_pddrc_config(pddrc_path)
                        context_name = context_override or resolved_context_name
                        if not context_name:
                            arch_context_path = code_path
                            context_name = (
                                _detect_context(arch_context_path, config, None)
                                or _detect_context(Path.cwd(), config, None)
                            )
                        context_config = config.get('contexts', {}).get(context_name or '', {})
                        defaults = context_config.get('defaults', {})
                        example_dir = defaults.get('example_output_path', 'examples/')
                        test_dir = defaults.get('test_output_path', 'tests/')
                        generate_dir = defaults.get('generate_output_path', '')
                        configured_outputs = defaults.get('outputs', {})
                        if isinstance(configured_outputs, dict):
                            outputs_config = configured_outputs
                        if example_dir and not example_dir.endswith('/'):
                            example_dir = example_dir + '/'
                        if test_dir and not test_dir.endswith('/'):
                            test_dir = test_dir + '/'
                        if generate_dir and not generate_dir.endswith('/'):
                            generate_dir = generate_dir + '/'
                    except ValueError:
                        pass

                # Apply generate_output_path only when arch_filepath is a bare filename
                # at the project root (no directory component). When arch_filepath already
                # contains a subdirectory structure, that structure takes precedence.
                # Preserve the explicit filename (including extension) from architecture.json;
                # only the parent directory is overridden by .pddrc generate_output_path.
                arch_filepath_path = Path(arch_filepath)
                if generate_dir and str(arch_filepath_path.parent) in (".", ""):
                    code_path = project_root / f"{generate_dir}{arch_filepath_path.name}"
                    logger.debug(f"Path source: generate={code_path} (from pddrc generate_output_path)")
                else:
                    logger.debug(f"Path source: generate={code_path} (from architecture.json)")

                # Issue #1677: when the leaf basename is ambiguous (several architecture
                # modules share it, e.g. Next.js `page`), two path-qualified modules
                # (`app/login/page`, `app/settings/page`) would otherwise both write to
                # `examples/page_example.tsx` and `tests/test_page.tsx`. Derive the
                # example/test stem from the canonical code path so the artifacts are
                # distinct per module. Unique leaves keep the flat stem (backward compat).
                example_stem = code_stem
                if arch_path and len(_architecture_module_choices(arch_path, name, language, modules=arch_modules)) > 1:
                    example_stem = _safe_basename(Path(arch_filepath).with_suffix("").as_posix())

                example_path = project_root / f"{example_dir}{example_stem}_example{_dot(extension)}"
                test_path = project_root / f"{test_dir}test_{example_stem}{_dot(extension)}"
                configured_example = False
                configured_test = False

                # architecture.json owns the code destination, but exact .pddrc
                # example/test templates still own those artifact destinations.
                # Do this before legacy basename-existing-file preferences so a
                # configured path is never silently replaced by a conventional one.
                if outputs_config:
                    template_paths = _generate_paths_from_templates(
                        basename=construct_paths_basename,
                        language=language,
                        extension=extension,
                        outputs_config=outputs_config,
                        prompt_path=prompt_path,
                    )
                    for artifact in ("example", "test"):
                        if artifact not in outputs_config or artifact not in template_paths:
                            continue
                        configured_path = template_paths[artifact]
                        if not configured_path.is_absolute():
                            configured_path = project_root / configured_path
                        if artifact == "example":
                            example_path = configured_path
                            configured_example = True
                        else:
                            test_path = configured_path
                            configured_test = True

                # If the flattened prompt basename already has corresponding example/test
                # artifacts, prefer those over the architecture filepath stem. This keeps
                # command summaries and sync behavior aligned with repos that intentionally
                # namespace files such as lib_sse_example.ts or test_api_route.ts.
                if name != code_stem and example_stem == code_stem:
                    basename_example_path = _find_named_file(
                        project_root / example_dir,
                        f"{name}_example{_dot(extension)}",
                    )
                    basename_test_path = _find_named_file(
                        project_root / test_dir,
                        f"test_{name}{_dot(extension)}",
                    )
                    preferred_example = False
                    preferred_test = False
                    if not configured_example and basename_example_path is not None:
                        example_path = basename_example_path
                        preferred_example = True
                    if not configured_test and basename_test_path is not None:
                        test_path = basename_test_path
                        preferred_test = True
                    if preferred_example or preferred_test:
                        logger.info(
                            "Preferring basename-derived artifacts for %s over architecture stem %s "
                            "(example=%s, test=%s)",
                            name,
                            code_stem,
                            preferred_example,
                            preferred_test,
                        )

                test_dir_path = test_path.parent
                test_stem = glob.escape(test_path.stem)
                if test_dir_path.exists():
                    matching_test_files = sorted(test_dir_path.glob(f"{test_stem}*.{extension}"))
                else:
                    matching_test_files = [test_path] if test_path.exists() else []

                result = {
                    'prompt': Path(prompt_path),
                    'code': code_path,
                    'example': example_path,
                    'test': test_path,
                    'test_files': matching_test_files or [test_path]
                }
                logger.info(f"get_pdd_file_paths returning (from architecture.json): {result}")
                return _finalize_output_paths(result)

        # Check if prompt file exists - if not, we still need configuration-aware paths
        if not Path(prompt_path).exists():
            # Use construct_paths with minimal inputs to get configuration-aware paths
            # even when prompt doesn't exist
            extension = get_extension(language)
            try:
                # Pass the (not-yet-existing) prompt path as an anchoring hint so
                # construct_paths locates the SUBPROJECT .pddrc (walking up from the
                # prompt dir) and resolves outputs against it — not the process CWD.
                # Without this, a new module resolved from a parent/sibling CWD writes
                # code/test under the parent instead of the project. _find_pddrc_file
                # only walks parent dirs, so the file need not exist.
                resolved_config, _, output_paths, _ = construct_paths(
                    input_file_paths={"prompt_file": prompt_path},
                    force=True,
                    quiet=True,
                    command="sync",
                    command_options={"basename": construct_paths_basename, "language": language},
                    context_override=context_override,
                    path_resolution_mode="cwd"
                )

                import logging
                logger = logging.getLogger(__name__)
                logger.info(f"resolved_config: {resolved_config}")
                logger.info(f"output_paths: {output_paths}")

                # Issue #237: Check for 'outputs' config for template-based path generation
                outputs_config = resolved_config.get('outputs')
                if outputs_config:
                    logger.info(f"Using template-based paths from outputs config")
                    context_name = context_override or resolved_config.get('_matched_context')
                    basename_for_templates = _relative_basename_for_context(basename, context_name, prompts_root_anchor)
                    result = _generate_paths_from_templates(
                        basename=basename_for_templates,
                        language=language,
                        extension=extension,
                        outputs_config=outputs_config,
                        prompt_path=prompt_path
                    )
                    result = _overlay_configured_output_paths(
                        result,
                        outputs_config,
                        output_paths,
                        basename,
                        language,
                        context_name=context_name,
                        pddrc_anchor=prompts_root_anchor,
                    )
                    # Template paths are project-relative; anchor them at the
                    # subproject (the .pddrc directory) so a new module resolved from a
                    # parent/sibling CWD writes under the project, not the CWD.
                    _new_pddrc = _find_pddrc_file(config_anchor)
                    if _new_pddrc is not None:
                        result = _anchor_output_paths_at_project(result, _new_pddrc.parent)
                    logger.debug(f"get_pdd_file_paths returning (template-based): {result}")
                    return _finalize_output_paths(result)

                # Legacy path construction (backwards compatibility)
                # Extract directory configuration from resolved_config
                # Note: construct_paths sets tests_dir, examples_dir, code_dir keys
                test_dir = resolved_config.get('tests_dir', 'tests/')
                example_dir = resolved_config.get('examples_dir', 'examples/')
                code_dir = resolved_config.get('code_dir', './')

                logger.info(f"Extracted dirs - test: {test_dir}, example: {example_dir}, code: {code_dir}")

                # Ensure directories end with /
                if test_dir and not test_dir.endswith('/'):
                    test_dir = test_dir + '/'
                if example_dir and not example_dir.endswith('/'):
                    example_dir = example_dir + '/'
                if code_dir and not code_dir.endswith('/'):
                    code_dir = code_dir + '/'

                # Extract directory and name parts for subdirectory basename support
                dir_prefix, name_part = _extract_name_part(construct_paths_basename)

                # Get explicit config paths (these are the SOURCE OF TRUTH when configured)
                # These should be used directly, NOT combined with dir_prefix
                generate_output_path = resolved_config.get('generate_output_path', '')
                example_output_path = resolved_config.get('example_output_path', '')
                test_output_path = resolved_config.get('test_output_path', '')

                # Construct paths: use explicit config paths directly when configured,
                # otherwise fall back to old behavior with dir_prefix for backwards compat

                # Code path
                if generate_output_path and generate_output_path.endswith('/'):
                    # Explicit complete directory - use directly with just filename
                    code_path = f"{generate_output_path}{name_part}{_dot(extension)}"
                else:
                    # The shared re-anchor below adds dir_prefix exactly once.
                    code_path = f"{code_dir}{name_part}{_dot(extension)}"

                # Example path
                if example_output_path and example_output_path.endswith('/'):
                    # Explicit complete directory - use directly with just filename
                    example_path = f"{example_output_path}{name_part}_example{_dot(extension)}"
                else:
                    # The shared re-anchor below adds dir_prefix exactly once.
                    example_path = f"{example_dir}{name_part}_example{_dot(extension)}"

                # Test path
                if test_output_path and test_output_path.endswith('/'):
                    # Explicit complete directory - use directly with just filename
                    test_path = f"{test_output_path}test_{name_part}{_dot(extension)}"
                else:
                    # The shared re-anchor below adds dir_prefix exactly once.
                    test_path = f"{test_dir}test_{name_part}{_dot(extension)}"

                logger.debug(f"Final paths: test={test_path}, example={example_path}, code={code_path}")

                # Convert to Path objects
                test_path = Path(test_path)
                example_path = Path(example_path)
                code_path = Path(code_path)

                # Issue #1677: keep a path-qualified basename's subdirectory (this branch
                # only runs for a module with no architecture entry; see the prompt-exists
                # branch for the rationale and the shared-segment handling). The
                # CONTEXT-RELATIVE basename is used so a context whose prompts_dir already
                # maps the directory (e.g. `backend/utils/x` under context `backend-utils`)
                # is left to its configured generate_output_path, not re-prefixed.
                # An explicit output path ending in '/' is a COMPLETE directory (the
                # branches above already used it as-is): re-prefixing it with the
                # basename's subdir would double the path (e.g. backend/functions/utils/
                # + backend/utils/x -> .../utils/utils/x), so skip the re-anchor there.
                if not (generate_output_path and generate_output_path.endswith('/')):
                    code_path = _reanchor_under_basename_subdir(code_path, construct_paths_basename)
                if not (example_output_path and example_output_path.endswith('/')):
                    example_path = _reanchor_under_basename_subdir(example_path, construct_paths_basename)
                if not (test_output_path and test_output_path.endswith('/')):
                    test_path = _reanchor_under_basename_subdir(test_path, construct_paths_basename)

                # Bug #156: Find all matching test files
                test_dir_path = test_path.parent
                test_stem = f"test_{glob.escape(name_part)}"
                if test_dir_path.exists():
                    matching_test_files = sorted(test_dir_path.glob(f"{test_stem}*.{glob.escape(extension)}"))
                else:
                    matching_test_files = [test_path] if test_path.exists() else []

                result = {
                    'prompt': Path(prompt_path),
                    'code': code_path,
                    'example': example_path,
                    'test': test_path,
                    'test_files': matching_test_files or [test_path]  # Bug #156
                }
                logger.debug(f"get_pdd_file_paths returning (prompt missing): test={test_path}")
                return _finalize_output_paths(result)
            except AmbiguousModuleError:
                # A hard path-resolution error (ambiguity, unsafe/out-of-tree output
                # or prompt) MUST fail closed — never fall through to the convention
                # fallback below, which would silently return an unvalidated target.
                raise
            except Exception as e:
                # If construct_paths fails, fall back to convention-based paths. Anchor
                # them at the resolved subproject (the .pddrc directory) when it differs
                # from the process CWD, so a new module resolved from a parent/sibling CWD
                # does not land its code/example/test under the wrong root; when they
                # coincide the paths stay relative, preserving the legacy return contract.
                import logging
                logger = logging.getLogger(__name__)
                logger.debug(f"construct_paths failed for non-existent prompt, using defaults: {e}")
                dir_prefix, name_part = _extract_name_part(construct_paths_basename)
                _pddrc_fallback = _find_pddrc_file(config_anchor)
                _subproject = _pddrc_fallback.parent if _pddrc_fallback else None

                def _anchor_fallback(rel: str) -> Path:
                    rel_path = Path(rel)
                    if (
                        _subproject is not None
                        and _subproject.resolve(strict=False) != Path.cwd().resolve(strict=False)
                    ):
                        return _subproject / rel_path
                    return rel_path

                fallback_test_path = _anchor_fallback(f"{dir_prefix}test_{name_part}{_dot(extension)}")
                # Bug #156: Find matching test files even in fallback (under the anchored dir)
                fallback_test_dir = fallback_test_path.parent
                if fallback_test_dir.exists():
                    fallback_matching = sorted(
                        fallback_test_dir.glob(f"test_{glob.escape(name_part)}*.{glob.escape(extension)}")
                    )
                else:
                    fallback_matching = [fallback_test_path] if fallback_test_path.exists() else []
                return _finalize_output_paths({
                    'prompt': Path(prompt_path),
                    'code': _anchor_fallback(f"{dir_prefix}{name_part}{_dot(extension)}"),
                    'example': _anchor_fallback(f"{dir_prefix}{name_part}_example{_dot(extension)}"),
                    'test': fallback_test_path,
                    'test_files': fallback_matching or [fallback_test_path]  # Bug #156
                })
        
        input_file_paths = {
            "prompt_file": prompt_path
        }
        
        # Call construct_paths to get configuration-aware paths
        resolved_config, input_strings, output_file_paths, detected_language = construct_paths(
            input_file_paths=input_file_paths,
            force=True,  # Use force=True to avoid interactive prompts during sync
            quiet=True,
            command="sync",  # Use sync command to get more tolerant path handling
            command_options={"basename": construct_paths_basename, "language": language},
            context_override=context_override,
            path_resolution_mode="cwd"
        )

        # Issue #237: Check for 'outputs' config for template-based path generation
        # This must be checked even when prompt EXISTS (not just when it doesn't exist)
        outputs_config = resolved_config.get('outputs')
        # R16: reject unsafe .pddrc output templates on the EFFECTIVE resolved config
        # (construct_paths may select a nearer descendant .pddrc than config_anchor).
        _reject_unsafe_outputs_templates(outputs_config, _governing_root)
        if outputs_config:
            extension = get_extension(language)
            logger.info(f"Using template-based paths from outputs config (prompt exists)")
            context_name = context_override or resolved_config.get('_matched_context')
            basename_for_templates = _relative_basename_for_context(basename, context_name, prompts_root_anchor)
            result = _generate_paths_from_templates(
                basename=basename_for_templates,
                language=language,
                extension=extension,
                outputs_config=outputs_config,
                prompt_path=prompt_path
            )
            result = _overlay_configured_output_paths(
                result,
                outputs_config,
                output_file_paths,
                basename,
                language,
                context_name=context_name,
                pddrc_anchor=prompts_root_anchor,
            )
            # Anchor project-relative template outputs at the subproject (as the
            # missing-prompt branch does) so an existing prompt resolved from a
            # parent/sibling CWD still writes code/example/test under the project.
            _existing_pddrc = _find_pddrc_file(config_anchor)
            if _existing_pddrc is not None:
                result = _anchor_output_paths_at_project(result, _existing_pddrc.parent)
            logger.debug(f"get_pdd_file_paths returning (template-based, prompt exists): {result}")
            return _finalize_output_paths(result)

        # For sync command, output_file_paths contains the configured paths
        # Extract the code path from output_file_paths
        code_path = output_file_paths.get('generate_output_path', '')
        if not code_path:
            # Try other possible keys
            code_path = output_file_paths.get('output', output_file_paths.get('code_file', ''))
        if not code_path:
            # Fallback to constructing from basename with configuration
            extension = get_extension(language)
            generate_output_path = resolved_config.get('generate_output_path', '')
            dir_prefix, name_part = _extract_name_part(basename)

            # Use explicit config path directly when configured (ending with /)
            if generate_output_path and generate_output_path.endswith('/'):
                code_path = f"{generate_output_path}{name_part}{_dot(extension)}"
            else:
                # Old behavior - use path + dir_prefix
                code_dir = generate_output_path or './'
                if not code_dir.endswith('/'):
                    code_dir = code_dir + '/'
                code_path = f"{code_dir}{dir_prefix}{name_part}{_dot(extension)}"
        
        # Get configured paths for example and test files using construct_paths
        # Note: construct_paths requires files to exist, so we need to handle the case
        # where code file doesn't exist yet (during initial sync startup)
        try:
            # Create a temporary empty code file if it doesn't exist for path resolution
            code_path_obj = Path(code_path)
            temp_code_created = False
            # Never materialize a probe file outside the governing project: a
            # .pddrc generate_output_path that resolves outside the trusted root
            # (traversal, sibling-of-project under a parent CWD, or an away-pointing
            # absolute path) must not create directories out of tree here. When the
            # target is not within the governing root, skip the probe — the
            # containment guard on the return value fails the resolution closed.
            if not code_path_obj.exists() and _output_path_within_root(
                code_path_obj, _governing_root
            ):
                code_path_obj.parent.mkdir(parents=True, exist_ok=True)
                code_path_obj.touch()
                temp_code_created = True
            
            try:
                # Get example path using example command
                # Pass path_resolution_mode="cwd" so paths resolve relative to CWD (not project root)
                # Pass basename in command_options to preserve subdirectory structure
                _, _, example_output_paths, _ = construct_paths(
                    input_file_paths={"prompt_file": prompt_path, "code_file": code_path},
                    force=True, quiet=True, command="example",
                    command_options={"basename": basename},
                    context_override=context_override,
                    path_resolution_mode="cwd"
                )
                dir_prefix, name_part = _extract_name_part(basename)
                example_path = Path(example_output_paths.get('output', f"{dir_prefix}{name_part}_example{_dot(get_extension(language))}"))

                # Get test path using test command - handle case where test file doesn't exist yet
                # Pass basename in command_options to preserve subdirectory structure
                try:
                    _, _, test_output_paths, _ = construct_paths(
                        input_file_paths={"prompt_file": prompt_path, "code_file": code_path},
                        force=True, quiet=True, command="test",
                        command_options={"basename": basename},
                        context_override=context_override,
                        path_resolution_mode="cwd"
                    )
                    test_path = Path(test_output_paths.get('output', f"{dir_prefix}test_{name_part}{_dot(get_extension(language))}"))
                except FileNotFoundError:
                    # Test file doesn't exist yet - create default path
                    test_path = Path(f"{dir_prefix}test_{name_part}{_dot(get_extension(language))}")
                
            finally:
                # Clean up temporary file if we created it
                if temp_code_created and code_path_obj.exists() and code_path_obj.stat().st_size == 0:
                    code_path_obj.unlink()

        except AmbiguousModuleError:
            # A hard path-resolution error (unsafe/out-of-tree target) must fail
            # closed, not degrade into the convention fallback below.
            raise
        except Exception as e:
            # Log the specific exception that's causing fallback to wrong paths
            import logging
            logger = logging.getLogger(__name__)
            logger.warning(f"construct_paths failed in get_pdd_file_paths: {type(e).__name__}: {e}")
            logger.warning(f"Falling back to .pddrc-aware path construction")
            logger.warning(f"prompt_path: {prompt_path}, code_path: {code_path}")
            
            # Improved fallback: try to use construct_paths with just prompt_file to get proper directory configs
            try:
                # Get configured directories by using construct_paths with just the prompt file
                # Pass path_resolution_mode="cwd" so paths resolve relative to CWD (not project root)
                # Pass basename in command_options to preserve subdirectory structure
                _, _, example_output_paths, _ = construct_paths(
                    input_file_paths={"prompt_file": prompt_path},
                    force=True, quiet=True, command="example",
                    command_options={"basename": basename},
                    context_override=context_override,
                    path_resolution_mode="cwd"
                )
                dir_prefix, name_part = _extract_name_part(basename)
                example_path = Path(example_output_paths.get('output', f"{dir_prefix}{name_part}_example{_dot(get_extension(language))}"))

                try:
                    _, _, test_output_paths, _ = construct_paths(
                        input_file_paths={"prompt_file": prompt_path},
                        force=True, quiet=True, command="test",
                        command_options={"basename": basename},
                        context_override=context_override,
                        path_resolution_mode="cwd"
                    )
                    test_path = Path(test_output_paths.get('output', f"{dir_prefix}test_{name_part}{_dot(get_extension(language))}"))
                except Exception:
                    # If test path construction fails, use default naming
                    test_path = Path(f"{dir_prefix}test_{name_part}{_dot(get_extension(language))}")
                
            except Exception:
                # Final fallback to deriving from code path if all else fails
                code_path_obj = Path(code_path)
                code_dir = code_path_obj.parent
                code_stem = code_path_obj.stem
                code_ext = code_path_obj.suffix
                example_path = code_dir / f"{code_stem}_example{code_ext}"
                test_path = code_dir / f"test_{code_stem}{code_ext}"
        
        # Issue #1677: this path runs only for a module with NO architecture entry
        # (registered modules return from the architecture branch above). construct_paths
        # collapses a path-qualified basename to its bare leaf, so a new `foo/page` would
        # write to src/page.tsx / examples/page_example.tsx — colliding with any other
        # `*/page`. Re-anchor under the CONTEXT-RELATIVE basename subdirectory so a
        # context whose prompts_dir already maps the directory is left to its configured
        # generate_output_path (not re-prefixed / duplicated).
        code_path = _reanchor_under_basename_subdir(code_path, construct_paths_basename)
        example_path = _reanchor_under_basename_subdir(example_path, construct_paths_basename)
        test_path = _reanchor_under_basename_subdir(test_path, construct_paths_basename)

        # Ensure all paths are Path objects
        if isinstance(code_path, str):
            code_path = Path(code_path)

        # Keep paths as they are (absolute or relative as returned by construct_paths)
        # This ensures consistency with how construct_paths expects them

        # Bug #156: Find all matching test files
        test_dir = test_path.parent
        _, name_part_for_glob = _extract_name_part(basename)
        test_stem = f"test_{glob.escape(name_part_for_glob)}"
        extension = get_extension(language)
        if test_dir.exists():
            matching_test_files = sorted(test_dir.glob(f"{test_stem}*.{glob.escape(extension)}"))
        else:
            matching_test_files = [test_path] if test_path.exists() else []

        return _finalize_output_paths({
            'prompt': Path(prompt_path),
            'code': code_path,
            'example': example_path,
            'test': test_path,
            'test_files': matching_test_files or [test_path]  # Bug #156: All matching test files
        })

    except AmbiguousModuleError:
        # Issue #1677: ambiguity is a hard, actionable error — never let the broad
        # fallback below swallow it into a (wrong) default path.
        raise
    except Exception as e:
        # Fallback to simple naming if construct_paths fails
        extension = get_extension(language)
        dir_prefix, name_part = _extract_name_part(basename)
        test_path = Path(f"{dir_prefix}test_{name_part}{_dot(extension)}")
        # Bug #156: Try to find matching test files even in fallback
        test_dir = Path('.')
        test_stem = f"{glob.escape(dir_prefix)}test_{glob.escape(name_part)}"
        if test_dir.exists():
            matching_test_files = sorted(test_dir.glob(f"{test_stem}*.{glob.escape(extension)}"))
        else:
            matching_test_files = [test_path] if test_path.exists() else []
        prompts_root = _resolve_prompts_root(prompts_dir)
        # Case-insensitive prompt file lookup for fallback path
        fallback_prompt_path = prompts_root / f"{basename}_{language}.prompt"
        if not fallback_prompt_path.exists() and prompts_root.is_dir():
            target_lower = fallback_prompt_path.name.lower()
            for candidate in prompts_root.iterdir():
                if candidate.name.lower() == target_lower and candidate.is_file():
                    fallback_prompt_path = candidate
                    break
        _outer_fallback = {
            'prompt': fallback_prompt_path,
            'code': Path(f"{dir_prefix}{name_part}{_dot(extension)}"),
            'example': Path(f"{dir_prefix}{name_part}_example{_dot(extension)}"),
            'test': test_path,
            'test_files': matching_test_files or [test_path]  # Bug #156: All matching test files
        }
        # Even this last-resort fallback must be anchored under the governing root
        # and contained — otherwise a parent/sibling CWD makes these relative
        # basename paths resolve outside the project. Route it through the same
        # finalizer. If resolution failed so early that the finalizer/governing
        # root were never established (e.g. a pathological prompts_dir that could
        # not be resolved), fail closed rather than return unvalidated CWD-relative
        # paths.
        try:
            return _finalize_output_paths(_outer_fallback)
        except NameError:
            raise UnsafePromptPathError(
                Path(str(prompts_dir)), Path.cwd()
            )


def calculate_sha256(file_path: Path) -> Optional[str]:
    """Calculates the SHA256 hash of a file if it exists."""
    if not file_path.exists():
        return None
    
    try:
        hasher = hashlib.sha256()
        with open(file_path, 'rb') as f:
            for chunk in iter(lambda: f.read(4096), b""):
                hasher.update(chunk)
        return hasher.hexdigest()
    except (IOError, OSError):
        return None


_INCLUDE_PATTERN = re.compile(r'<include\b[^>]*>(.*?)</include>')
_BACKTICK_INCLUDE_PATTERN = re.compile(r'```<([^>]*?)>```')


def _resolve_include_path(include_ref: str, prompt_dir: Path) -> Optional[Path]:
    """Resolve an <include> reference to an absolute Path."""
    p = Path(include_ref)
    if p.is_absolute() and p.exists():
        return p
    candidate = prompt_dir / include_ref
    if candidate.exists():
        return candidate
    candidate = Path.cwd() / include_ref
    if candidate.exists():
        return candidate
    return None


def extract_include_deps(prompt_path: Path) -> Dict[str, str]:
    """Extract include dependency paths and their hashes from a prompt file.

    Returns a dict mapping resolved dependency paths to their SHA256 hashes.
    Only includes dependencies that exist on disk.
    """
    if not prompt_path.exists():
        return {}

    try:
        prompt_content = prompt_path.read_text(encoding='utf-8', errors='ignore')
    except (IOError, OSError):
        return {}

    include_refs = _INCLUDE_PATTERN.findall(prompt_content)
    include_refs += _BACKTICK_INCLUDE_PATTERN.findall(prompt_content)

    if not include_refs:
        return {}

    deps = {}
    prompt_dir = prompt_path.parent
    for ref in sorted(set(r.strip() for r in include_refs)):
        dep_path = _resolve_include_path(ref, prompt_dir)
        if dep_path and dep_path.exists():
            dep_hash = calculate_sha256(dep_path)
            if dep_hash:
                try:
                    rel_path = dep_path.relative_to(Path.cwd())
                except ValueError:
                    rel_path = dep_path
                deps[str(rel_path)] = dep_hash

    return deps


def calculate_prompt_hash(prompt_path: Path, stored_deps: Optional[Dict[str, str]] = None) -> Optional[str]:
    """Hash a prompt file including the content of all its <include> dependencies.

    If the prompt has <include> tags, extracts and hashes those dependencies.
    If no tags are found but stored_deps is provided (from a previous fingerprint),
    uses those stored dependency paths to compute the hash. This handles the case
    where the auto-deps step strips <include> tags from the prompt file.

    Args:
        prompt_path: Path to the prompt file.
        stored_deps: Previously stored dependency paths from fingerprint (issue #522).

    Returns:
        SHA256 hex digest of the prompt + dependency contents, or None.
    """
    if not prompt_path.exists():
        return None

    try:
        prompt_content = prompt_path.read_text(encoding='utf-8', errors='ignore')
    except (IOError, OSError):
        return None

    # Try to find include refs in current prompt content
    include_refs = _INCLUDE_PATTERN.findall(prompt_content)
    include_refs += _BACKTICK_INCLUDE_PATTERN.findall(prompt_content)

    # Resolve to actual paths
    prompt_dir = prompt_path.parent
    dep_paths = []
    if include_refs:
        for ref in sorted(set(r.strip() for r in include_refs)):
            dep_path = _resolve_include_path(ref, prompt_dir)
            if dep_path and dep_path.exists():
                dep_paths.append(dep_path)
    elif stored_deps:
        # No include tags in prompt — use stored dependency paths from fingerprint
        for dep_path_str in sorted(stored_deps.keys()):
            dep_path = Path(dep_path_str)
            if dep_path.exists():
                dep_paths.append(dep_path)

    if not dep_paths:
        return calculate_sha256(prompt_path)

    # Build composite hash: prompt bytes + sorted dependency contents
    hasher = hashlib.sha256()
    try:
        with open(prompt_path, 'rb') as f:
            for chunk in iter(lambda: f.read(4096), b""):
                hasher.update(chunk)
    except (IOError, OSError):
        return None

    for dep_path in dep_paths:
        try:
            with open(dep_path, 'rb') as f:
                for chunk in iter(lambda: f.read(4096), b""):
                    hasher.update(chunk)
        except (IOError, OSError):
            pass

    return hasher.hexdigest()


def read_fingerprint(
    basename: str,
    language: str,
    paths: Optional[Dict[str, Path]] = None,
) -> Optional[Fingerprint]:
    """Reads and validates the JSON fingerprint file.

    `paths` (Issue #1211): when provided, the meta directory is resolved
    via upward .pddrc detection from those file paths so subprojects whose
    .pddrc lives BELOW run CWD are honored.
    """
    meta_dir = get_meta_dir(paths=paths)
    meta_dir.mkdir(parents=True, exist_ok=True)
    fingerprint_file = meta_dir / f"{_safe_basename(basename)}_{language.lower()}.json"
    
    if not fingerprint_file.exists():
        return None
    
    try:
        with open(fingerprint_file, 'r') as f:
            data = json.load(f)
        
        return Fingerprint(
            pdd_version=data['pdd_version'],
            timestamp=data['timestamp'],
            command=data['command'],
            prompt_hash=data.get('prompt_hash'),
            code_hash=data.get('code_hash'),
            example_hash=data.get('example_hash'),
            test_hash=data.get('test_hash'),
            test_files=data.get('test_files'),  # Bug #156
            include_deps=data.get('include_deps'),  # Issue #522
        )
    except (json.JSONDecodeError, KeyError, IOError):
        return None


def read_run_report(
    basename: str,
    language: str,
    paths: Optional[Dict[str, Path]] = None,
) -> Optional[RunReport]:
    """Reads and validates the JSON run report file.

    `paths` (Issue #1211): when provided, the meta directory is resolved
    via upward .pddrc detection from those file paths so subprojects whose
    .pddrc lives BELOW run CWD are honored.
    """
    meta_dir = get_meta_dir(paths=paths)
    meta_dir.mkdir(parents=True, exist_ok=True)
    run_report_file = meta_dir / f"{_safe_basename(basename)}_{language.lower()}_run.json"
    
    if not run_report_file.exists():
        return None
    
    try:
        with open(run_report_file, 'r') as f:
            data = json.load(f)
        
        return RunReport(
            timestamp=data['timestamp'],
            exit_code=data['exit_code'],
            tests_passed=data['tests_passed'],
            tests_failed=data['tests_failed'],
            coverage=data['coverage'],
            test_hash=data.get('test_hash'),  # Optional for backward compatibility
            test_files=data.get('test_files')  # Bug #156
        )
    except (json.JSONDecodeError, KeyError, IOError):
        return None


def calculate_current_hashes(paths: Dict[str, Any], stored_include_deps: Optional[Dict[str, str]] = None) -> Dict[str, Any]:
    """Computes the hashes for all current files on disk.

    Args:
        paths: Dictionary of PDD file paths.
        stored_include_deps: Previously stored include dependency paths from fingerprint.
            Used when the prompt no longer has <include> tags (issue #522).
    """
    hashes = {}
    for file_type, file_path in paths.items():
        if file_type == 'test_files':
            # Bug #156: Calculate hashes for all test files
            hashes['test_files'] = {
                f.name: calculate_sha256(f)
                for f in file_path
                if isinstance(f, Path) and f.exists()
            }
        elif file_type == 'prompt' and isinstance(file_path, Path):
            # Issue #522: Hash prompt with <include> dependencies
            hashes['prompt_hash'] = calculate_prompt_hash(file_path, stored_deps=stored_include_deps)
            # Also extract current include deps for persistence
            hashes['include_deps'] = extract_include_deps(file_path)
            # If no deps found in prompt but we have stored deps, preserve them
            if not hashes['include_deps'] and stored_include_deps:
                # Re-hash stored deps to check for changes
                updated_deps = {}
                for dep_path_str, old_hash in stored_include_deps.items():
                    dep_path = Path(dep_path_str)
                    if dep_path.exists():
                        new_hash = calculate_sha256(dep_path)
                        if new_hash:
                            updated_deps[dep_path_str] = new_hash
                hashes['include_deps'] = updated_deps
        elif isinstance(file_path, Path):
            hashes[f"{file_type}_hash"] = calculate_sha256(file_path)
    return hashes


def get_git_diff(file_path: Path) -> str:
    """Get git diff for a file against HEAD."""
    try:
        result = subprocess.run(
            ['git', 'diff', 'HEAD', str(file_path)],
            capture_output=True,
            text=True,
            cwd=file_path.parent if file_path.parent.exists() else Path.cwd()
        )
        
        if result.returncode == 0:
            return result.stdout
        else:
            return ""
    except (subprocess.SubprocessError, FileNotFoundError):
        return ""


def estimate_operation_cost(operation: str, language: str = "python") -> float:
    """Returns estimated cost in dollars for each operation based on typical LLM usage."""
    cost_map = {
        'auto-deps': 0.10,
        'generate': 0.50,
        'example': 0.30,
        'crash': 0.40,
        'verify': 0.35,
        'test': 0.60,
        'test_extend': 0.60,  # Same cost as test - generates additional tests
        'fix': 0.45,
        'update': 0.25,
        'nothing': 0.0,
        'all_synced': 0.0,
        'error': 0.0,
        'fail_and_request_manual_merge': 0.0
    }
    return cost_map.get(operation, 0.0)


def _changed_artifacts_from_hashes(
    fingerprint: Fingerprint,
    paths: Dict[str, Path],
    current_hashes: Dict[str, Any],
) -> List[str]:
    """Return artifact names whose current hashes differ from a fingerprint."""
    changes: List[str] = []
    if current_hashes.get('prompt_hash') != fingerprint.prompt_hash:
        changes.append('prompt')
    if paths.get('code') and paths['code'].exists() and current_hashes.get('code_hash') != fingerprint.code_hash:
        changes.append('code')
    if paths.get('example') and paths['example'].exists() and current_hashes.get('example_hash') != fingerprint.example_hash:
        changes.append('example')
    if paths.get('test') and paths['test'].exists() and current_hashes.get('test_hash') != fingerprint.test_hash:
        changes.append('test')
    return changes


def _prompt_derived_conflict_decision(
    *,
    basename: str,
    language: str,
    changes: List[str],
    paths: Dict[str, Path],
    fingerprint: Optional[Fingerprint],
    read_only: bool,
) -> SyncDecision:
    """Return the explicit conflict decision for prompt+derived co-edits."""
    meta_dir = get_meta_dir(paths=paths)
    safe_bn = _safe_basename(basename)
    fp_path = meta_dir / f"{safe_bn}_{language.lower()}.json"
    rr_path = meta_dir / f"{safe_bn}_{language.lower()}_run.json"
    return SyncDecision(
        operation='fail_and_request_manual_merge',
        reason='Prompt and derived artifacts changed since the last fingerprint; manual conflict resolution required',
        confidence=1.0,
        estimated_cost=estimate_operation_cost('fail_and_request_manual_merge'),
        details={
            'decision_type': 'heuristic',
            'classification': 'CONFLICT',
            'changed_files': changes,
            'read_only': read_only,
            'metadata_preserved': [
                str(path) for path in (fp_path, rr_path) if path.exists()
            ],
            'fingerprint_found': fingerprint is not None,
        },
    )


def validate_expected_files(fingerprint: Optional[Fingerprint], paths: Dict[str, Path]) -> Dict[str, bool]:
    """
    Validate that files expected to exist based on fingerprint actually exist.
    
    Args:
        fingerprint: The last known good state fingerprint
        paths: Dict mapping file types to their expected Path objects
    
    Returns:
        Dict mapping file types to existence status
    """
    validation = {}
    
    if not fingerprint:
        return validation
    
    # Check each file type that has a hash in the fingerprint
    if fingerprint.code_hash:
        validation['code'] = paths['code'].exists()
    if fingerprint.example_hash:
        validation['example'] = paths['example'].exists()
    if fingerprint.test_hash:
        validation['test'] = paths['test'].exists()
        
    return validation


def _handle_missing_expected_files(
    missing_files: List[str], 
    paths: Dict[str, Path], 
    fingerprint: Fingerprint,
    basename: str, 
    language: str, 
    prompts_dir: str,
    skip_tests: bool = False,
    skip_verify: bool = False,
    isolated_replay_or_repair: bool = False,
) -> SyncDecision:
    """
    Handle the case where expected files are missing.
    Determine the appropriate recovery operation.
    
    Args:
        missing_files: List of file types that are missing
        paths: Dict mapping file types to their expected Path objects
        fingerprint: The last known good state fingerprint
        basename: The base name for the PDD unit
        language: The programming language
        prompts_dir: Directory containing prompt files
        skip_tests: If True, skip test generation
        skip_verify: If True, skip verification operations
    
    Returns:
        SyncDecision object with the appropriate recovery operation
    """
    
    # Priority: regenerate from the earliest missing component
    if 'code' in missing_files:
        # Code file missing - start from the beginning
        if paths['prompt'].exists():
            prompt_content = paths['prompt'].read_text(encoding='utf-8', errors='ignore')
            if check_for_dependencies(prompt_content):
                return SyncDecision(
                    operation='auto-deps',
                    reason='Code file missing, prompt has dependencies - regenerate from auto-deps',
                    confidence=1.0,
                    estimated_cost=estimate_operation_cost('auto-deps'),
                    details={
                        'decision_type': 'heuristic',
                        'missing_files': missing_files, 
                        'prompt_path': str(paths['prompt']),
                        'has_dependencies': True
                    }
                )
            else:
                return SyncDecision(
                    operation='generate',
                    reason='Code file missing - regenerate from prompt',
                    confidence=1.0,
                    estimated_cost=estimate_operation_cost('generate'),
                    details={
                        'decision_type': 'heuristic',
                        'missing_files': missing_files, 
                        'prompt_path': str(paths['prompt']),
                        'has_dependencies': False
                    }
                )
    
    elif 'example' in missing_files and paths['code'].exists():
        if isolated_replay_or_repair:
            return SyncDecision(
                operation='generate',
                reason='Example file missing but isolated repair/replay requested - regenerate code without unrelated example work',
                confidence=1.0,
                estimated_cost=estimate_operation_cost('generate'),
                details={
                    'decision_type': 'heuristic',
                    'missing_files': missing_files,
                    'code_path': str(paths['code']),
                    'isolated_replay_or_repair': True
                }
            )
        # Code exists but example missing
        return SyncDecision(
            operation='example',
            reason='Example file missing - regenerate example',
            confidence=1.0,
            estimated_cost=estimate_operation_cost('example'),
            details={
                'decision_type': 'heuristic',
                'missing_files': missing_files, 
                'code_path': str(paths['code'])
            }
        )
    
    elif 'test' in missing_files and paths['code'].exists() and paths['example'].exists():
        # Code and example exist but test missing
        if skip_tests:
            # Skip test generation if --skip-tests flag is used
            return SyncDecision(
                operation='nothing',
                reason='Test file missing but --skip-tests specified - workflow complete',
                confidence=1.0,
                estimated_cost=estimate_operation_cost('nothing'),
                details={
                    'decision_type': 'heuristic',
                    'missing_files': missing_files, 
                    'skip_tests': True
                }
            )
        else:
            return SyncDecision(
                operation='test',
                reason='Test file missing - regenerate tests',
                confidence=1.0,
                estimated_cost=estimate_operation_cost('test'),
                details={
                    'decision_type': 'heuristic',
                    'missing_files': missing_files, 
                    'code_path': str(paths['code'])
                }
            )
    
    # Fallback - regenerate everything
    return SyncDecision(
        operation='generate',
        reason='Multiple files missing - regenerate from prompt',
        confidence=1.0,
        estimated_cost=estimate_operation_cost('generate'),
        details={
            'decision_type': 'heuristic',
            'missing_files': missing_files
        }
    )


def _is_workflow_complete(paths: Dict[str, Path], skip_tests: bool = False, skip_verify: bool = False,
                          basename: str = None, language: str = None) -> bool:
    """
    Check if workflow is complete considering skip flags.

    Args:
        paths: Dict mapping file types to their expected Path objects
        skip_tests: If True, test files are not required for completion
        skip_verify: If True, verification operations are not required
        basename: Module basename (required for run_report check)
        language: Module language (required for run_report check)

    Returns:
        True if all required files exist AND have been validated (run_report exists)
    """
    required_files = ['code', 'example']

    if not skip_tests:
        required_files.append('test')

    # Check all required files exist
    if not all(paths[f].exists() for f in required_files):
        return False

    if skip_tests and skip_verify:
        return True

    # Also check that run_report exists and code works (exit_code == 0)
    # Without this, newly generated code would incorrectly be marked as "complete"
    if basename and language:
        run_report = read_run_report(basename, language, paths=paths)

        # Bug #349: If tests passed, consider workflow complete even if exit_code != 0
        # This handles cases where tooling (like pytest-cov) returns non-zero exit code
        # despite all tests passing.
        if not run_report:
            return False
            
        # Check for success: either exit_code is 0 OR tests passed successfully
        is_success = (run_report.exit_code == 0) or (run_report.tests_passed > 0 and run_report.tests_failed == 0)

        if not is_success:
            return False

        # Bug #573: Reject coverage=0.0 with passing tests — this indicates tests
        # are not actually exercising the module (e.g. sys.modules stubs masking
        # broken imports). Coverage of exactly 0.0 with passing tests is never valid.
        if run_report.tests_passed > 0 and run_report.coverage == 0.0:
            return False

        # Check that run_report corresponds to current test files (staleness detection)
        # If any test file changed since run_report was created, we can't trust the results
        if not skip_tests:
            # Bug #156: Check ALL test files, not just the primary one
            if 'test_files' in paths and run_report.test_files:
                # New multi-file comparison
                current_test_hashes = {
                    f.name: calculate_sha256(f)
                    for f in paths['test_files']
                    if f.exists()
                }
                stored_test_hashes = run_report.test_files

                # Check if any test file changed or new ones added/removed
                if set(current_test_hashes.keys()) != set(stored_test_hashes.keys()):
                    return False  # Test files added or removed

                for fname, current_hash in current_test_hashes.items():
                    if stored_test_hashes.get(fname) != current_hash:
                        return False  # Test file content changed
            elif 'test' in paths and paths['test'].exists():
                # Backward compat: single file check
                current_test_hash = calculate_sha256(paths['test'])
                if run_report.test_hash and current_test_hash != run_report.test_hash:
                    # run_report was created for a different version of the test file
                    return False
                if not run_report.test_hash:
                    # Legacy run_report without test_hash - check fingerprint timestamp as fallback
                    fingerprint = read_fingerprint(basename, language, paths=paths)
                    if fingerprint:
                        # If fingerprint is newer than run_report, run_report might be stale
                        from datetime import datetime
                        try:
                            fp_time = datetime.fromisoformat(fingerprint.timestamp.replace('Z', '+00:00'))
                            rr_time = datetime.fromisoformat(run_report.timestamp.replace('Z', '+00:00'))
                            if fp_time > rr_time:
                                return False  # run_report predates fingerprint, might be stale
                        except (ValueError, AttributeError):
                            pass  # If timestamps can't be parsed, skip this check

        # Check verify has been done (unless skip_verify)
        # Without this, workflow would be "complete" after crash even though verify hasn't run
        # Bug #23 fix: Also check for 'skip:' prefix which indicates operation was skipped, not executed
        if not skip_verify:
            fingerprint = read_fingerprint(basename, language, paths=paths)
            if fingerprint:
                # If command starts with 'skip:', the operation was skipped, not completed
                if fingerprint.command.startswith('skip:'):
                    return False
                if fingerprint.command not in COMPLETED_VERIFY_COMMANDS:
                    return False

        # CRITICAL FIX: Check tests have been run (unless skip_tests)
        # Without this, workflow would be "complete" after verify even though tests haven't run
        # This prevents false positive success when skip_verify=True but tests are still required
        # Bug #23 fix: Also check for 'skip:' prefix which indicates operation was skipped, not executed
        if not skip_tests:
            fp = read_fingerprint(basename, language, paths=paths)
            if fp:
                # If command starts with 'skip:', the operation was skipped, not completed
                if fp.command.startswith('skip:'):
                    return False
                if fp.command not in COMPLETED_TEST_COMMANDS:
                    return False

    return True


def check_for_dependencies(prompt_content: str) -> bool:
    """Check if prompt contains actual dependency indicators that need auto-deps processing."""
    # Only check for specific XML tags that indicate actual dependencies
    xml_dependency_indicators = [
        '<include>',
        '<web>',
        '<shell>'
    ]
    
    # Check for explicit dependency management mentions
    explicit_dependency_indicators = [
        'auto-deps',
        'auto_deps',
        'dependencies needed',
        'requires dependencies',
        'include dependencies'
    ]
    
    prompt_lower = prompt_content.lower()
    
    # Check for XML tags (case-sensitive for proper XML)
    has_xml_deps = any(indicator in prompt_content for indicator in xml_dependency_indicators)
    
    # Check for explicit dependency mentions
    has_explicit_deps = any(indicator in prompt_lower for indicator in explicit_dependency_indicators)
    
    return has_xml_deps or has_explicit_deps


def _check_example_success_history(
    basename: str,
    language: str,
    paths: Optional[Dict[str, Path]] = None,
) -> bool:
    """
    Check if the example has run successfully before by examining historical fingerprints and run reports.

    Args:
        basename: The base name for the PDD unit
        language: The programming language
        paths: Optional path hints (Issue #1211) so meta dir resolves to the
            subproject .pdd/meta when invoked from a parent CWD.

    Returns:
        True if the example has run successfully before, False otherwise
    """
    meta_dir = get_meta_dir(paths=paths)

    # Strategy 1: Check if there's a fingerprint with 'verify' command (indicates successful example run)
    # Cache fingerprint and run report to avoid redundant I/O operations
    fingerprint = read_fingerprint(basename, language, paths=paths)
    current_run_report = read_run_report(basename, language, paths=paths)
    
    # Strategy 1: Check if there's a fingerprint with 'verify' command (indicates successful example run)
    if fingerprint and fingerprint.command == 'verify':
        return True
    
    # Strategy 2: Check current run report for successful runs (exit_code == 0)
    # Note: We check the current run report for successful history since it's updated
    # This allows for a simple check of recent success
    if current_run_report and current_run_report.exit_code == 0:
        return True
    
    # Strategy 2b: Look for historical run reports with exit_code == 0
    # Check all run report files in the meta directory that match the pattern
    run_report_pattern = f"{glob.escape(_safe_basename(basename))}_{language.lower()}_run"
    for file in meta_dir.glob(f"{run_report_pattern}*.json"):
        try:
            with open(file, 'r') as f:
                data = json.load(f)
            
            # If we find any historical run with exit_code == 0, the example has run successfully
            if data.get('exit_code') == 0:
                return True
        except (json.JSONDecodeError, KeyError, IOError):
            continue
    
    # Strategy 3: Check if fingerprint has example_hash and was created after successful operations
    # Commands that indicate example was working: 'example', 'verify', 'test', 'fix'
    if fingerprint and fingerprint.example_hash:
        successful_commands = {'example', 'verify', 'test', 'fix'}
        if fingerprint.command in successful_commands:
            # If the fingerprint was created after these commands, the example likely worked
            return True
    
    return False


def sync_determine_operation(
    basename: str,
    language: str,
    target_coverage: float,
    budget: float = 10.0,
    log_mode: bool = False,
    prompts_dir: str = "prompts",
    skip_tests: bool = False,
    skip_verify: bool = False,
    context_override: Optional[str] = None,
    read_only: bool = False,
    isolated_replay_or_repair: bool = False,
) -> SyncDecision:
    """
    Core decision-making function for sync operations with skip flag awareness.
    
    Args:
        basename: The base name for the PDD unit
        language: The programming language
        target_coverage: Desired test coverage percentage
        budget: Maximum budget for operations
        log_mode: If True, skip locking entirely for read-only analysis
        prompts_dir: Directory containing prompt files
        skip_tests: If True, skip test generation and execution
        skip_verify: If True, skip verification operations
        read_only: If True, do not mutate metadata while analyzing state
    
    Returns:
        SyncDecision object with the recommended operation
    """
    
    analysis_read_only = read_only or log_mode
    if log_mode or read_only:
        # Skip locking for read-only analysis
        return _perform_sync_analysis(
            basename, language, target_coverage, budget,
            prompts_dir, skip_tests, skip_verify, context_override,
            read_only=analysis_read_only,
            isolated_replay_or_repair=isolated_replay_or_repair,
        )
    else:
        # Normal exclusive locking for actual operations
        with SyncLock(basename, language) as lock:
            return _perform_sync_analysis(
                basename, language, target_coverage, budget,
                prompts_dir, skip_tests, skip_verify, context_override,
                read_only=analysis_read_only,
                isolated_replay_or_repair=isolated_replay_or_repair,
            )


def _perform_sync_analysis(
    basename: str,
    language: str,
    target_coverage: float,
    budget: float,
    prompts_dir: str = "prompts",
    skip_tests: bool = False,
    skip_verify: bool = False,
    context_override: Optional[str] = None,
    read_only: bool = False,
    isolated_replay_or_repair: bool = False,
) -> SyncDecision:
    """
    Perform the sync state analysis without locking concerns.
    
    Args:
        basename: The base name for the PDD unit
        language: The programming language
        target_coverage: Desired test coverage percentage
        budget: Maximum budget for operations
        prompts_dir: Directory containing prompt files
        skip_tests: If True, skip test generation and execution
        skip_verify: If True, skip verification operations
        read_only: If True, avoid metadata mutations while analyzing state
    
    Returns:
        SyncDecision object with the recommended operation
    """
    # 1. Check Runtime Signals First (Highest Priority)
    # Workflow Order (from whitepaper):
    # 1. auto-deps (find context/dependencies)
    # 2. generate (create code module)  
    # 3. example (create usage example)
    # 4. crash (resolve crashes if code doesn't run)
    # 5. verify (verify example runs correctly after crash fix)
    # 6. test (generate unit tests)
    # 7. fix (resolve bugs found by tests)
    # 8. update (sync changes back to prompt)
    
    # Issue #1211: resolve file paths first so fingerprint/run-report reads
    # below can locate the subproject .pdd/meta via upward .pddrc detection
    # from those paths — even when run CWD is above the subproject.
    try:
        _initial_paths = get_pdd_file_paths(
            basename, language, prompts_dir, context_override=context_override
        )
    except AmbiguousModuleError:
        # Issue #1677: propagate ambiguity so sync fails fast instead of silently
        # analyzing with empty paths and generating to the wrong module.
        raise
    except Exception:
        _initial_paths = {}

    # Read fingerprint early since we need it for crash verification
    fingerprint = read_fingerprint(basename, language, paths=_initial_paths)

    # Check if auto-deps just completed - ALWAYS regenerate code after auto-deps
    # This must be checked early, before any run_report processing, because:
    # 1. Old run_report (if exists) is stale and should be ignored
    # 2. auto-deps updates dependencies but doesn't regenerate code
    if fingerprint and fingerprint.command == 'auto-deps':
        paths = get_pdd_file_paths(basename, language, prompts_dir, context_override=context_override)
        return SyncDecision(
            operation='generate',
            reason='Auto-deps completed - regenerate code with updated prompt',
            confidence=0.90,
            estimated_cost=estimate_operation_cost('generate'),
            details={
                'decision_type': 'heuristic',
                'previous_command': 'auto-deps',
                'code_exists': paths['code'].exists() if paths.get('code') else False,
                'regenerate_after_autodeps': True
            }
        )

    run_report = read_run_report(basename, language, paths=_initial_paths)
    if run_report and skip_tests:
        # Ignore stale or failing cached test-results from run_report when skip_tests is active.
        # Also zero exit_code when it is paired with test failures: a non-zero exit_code whose
        # sibling tests_failed > 0 is from the test runner (e.g. pytest returning 1/2 on
        # failures), not a real runtime crash, so it must not drive fix/crash decisions when the
        # caller has explicitly requested that tests be skipped.  When tests_failed == 0 the
        # exit_code reflects a genuine runtime error (e.g. a crash fix that still fails) and
        # must be preserved so the crash-retry path at the fingerprint check can act on it.
        exit_code_from_tests = run_report.tests_failed > 0
        run_report = RunReport(
            timestamp=run_report.timestamp,
            exit_code=0 if exit_code_from_tests else run_report.exit_code,
            tests_passed=run_report.tests_passed,
            tests_failed=0,
            coverage=run_report.coverage,
            test_hash=run_report.test_hash,
            test_files=run_report.test_files
        )
    # Only process runtime signals (crash/fix/test) if we have a fingerprint
    # Without a fingerprint, run_report is stale/orphaned and should be ignored
    if run_report and fingerprint:
        # Check for prompt changes FIRST - prompt changes take priority over runtime signals
        # If the user modified the prompt, we need to regenerate regardless of runtime state
        if fingerprint:
            paths = get_pdd_file_paths(basename, language, prompts_dir, context_override=context_override)
            # Issue #522: Use stored include deps so changes to included files are detected
            # even when auto-deps has stripped <include> tags from the prompt
            current_prompt_hash = calculate_prompt_hash(paths['prompt'], stored_deps=fingerprint.include_deps)
            if current_prompt_hash and current_prompt_hash != fingerprint.prompt_hash:
                current_hashes = calculate_current_hashes(
                    paths,
                    stored_include_deps=fingerprint.include_deps,
                )
                changes = _changed_artifacts_from_hashes(fingerprint, paths, current_hashes)
                derived_changes = [change for change in changes if change != 'prompt']
                if derived_changes:
                    return _prompt_derived_conflict_decision(
                        basename=basename,
                        language=language,
                        changes=changes,
                        paths=paths,
                        fingerprint=fingerprint,
                        read_only=read_only,
                    )
                prompt_content = paths['prompt'].read_text(encoding='utf-8', errors='ignore') if paths['prompt'].exists() else ""
                has_deps = check_for_dependencies(prompt_content)
                return SyncDecision(
                    operation='auto-deps' if has_deps else 'generate',
                    reason='Prompt changed - regenerating (takes priority over runtime signals)',
                    confidence=0.95,
                    estimated_cost=estimate_operation_cost('generate'),
                    details={
                        'decision_type': 'heuristic',
                        'prompt_changed': True,
                        'previous_command': fingerprint.command,
                        'runtime_state_ignored': True
                    }
                )

        # Check if we just completed a crash operation and need verification FIRST
        # This takes priority over test failures because we need to verify the crash fix worked
        # BUT only proceed to verify if exit_code == 0 (crash fix succeeded)
        if fingerprint and fingerprint.command == 'crash' and not skip_verify:
            if run_report.exit_code != 0:
                # Crash fix didn't work - need to re-run crash
                return SyncDecision(
                    operation='crash',
                    reason=f'Previous crash operation failed (exit_code={run_report.exit_code}) - retry crash fix',
                    confidence=0.90,
                    estimated_cost=estimate_operation_cost('crash'),
                    details={
                        'decision_type': 'heuristic',
                        'previous_command': 'crash',
                        'exit_code': run_report.exit_code,
                        'workflow_stage': 'crash_retry'
                    }
                )
            return SyncDecision(
                operation='verify',
                reason='Previous crash operation completed - verify example runs correctly',
                confidence=0.90,
                estimated_cost=estimate_operation_cost('verify'),
                details={
                    'decision_type': 'heuristic',
                    'previous_command': 'crash',
                    'current_exit_code': run_report.exit_code,
                    'fingerprint_command': fingerprint.command
                }
            )
        
        # Check test failures (after crash verification check)
        if run_report.tests_failed > 0:
            # First check if the test file actually exists
            pdd_files = get_pdd_file_paths(basename, language, prompts_dir, context_override=context_override)
            test_file = pdd_files.get('test')

            # Only suggest 'fix' if test file exists
            if test_file and test_file.exists():
                return SyncDecision(
                    operation='fix',
                    reason=f'Test failures detected: {run_report.tests_failed} failed tests',
                    confidence=0.90,
                    estimated_cost=estimate_operation_cost('fix'),
                    details={
                        'decision_type': 'heuristic',
                        'tests_failed': run_report.tests_failed,
                        'exit_code': run_report.exit_code,
                        'coverage': run_report.coverage
                    }
                )
            # If test file doesn't exist but we have test failures in run report,
            # we need to generate the test first
            else:
                return SyncDecision(
                    operation='test',
                    reason='Test failures reported but test file missing - need to generate tests',
                    confidence=0.85,
                    estimated_cost=estimate_operation_cost('test'),
                    details={
                        'decision_type': 'heuristic',
                        'run_report_shows_failures': True,
                        'test_file_exists': False
                    }
                )
        
        # Then check for runtime crashes (only if no test failures)
        if run_report.exit_code != 0:
            # Bug #349: If tests passed, ignore non-zero exit code (likely tooling noise)
            # Only trigger crash/fix if tests actually failed or didn't run
            tests_passed_successfully = run_report.tests_passed > 0 and run_report.tests_failed == 0

            if not tests_passed_successfully:
                # Context-aware decision: prefer 'fix' over 'crash' when example has run successfully before
                has_example_run_successfully = _check_example_success_history(basename, language, paths=_initial_paths)

                if has_example_run_successfully:
                    return SyncDecision(
                        operation='fix',
                        reason='Runtime error detected but example has run successfully before - prefer fix over crash',
                        confidence=0.90,
                        estimated_cost=estimate_operation_cost('fix'),
                        details={
                            'decision_type': 'heuristic',
                            'exit_code': run_report.exit_code,
                            'timestamp': run_report.timestamp,
                            'example_success_history': True,
                            'decision_rationale': 'prefer_fix_over_crash'
                        }
                    )
                else:
                    return SyncDecision(
                        operation='crash',
                        reason='Runtime error detected in last run - no successful example history',
                        confidence=0.95,
                        estimated_cost=estimate_operation_cost('crash'),
                        details={
                            'decision_type': 'heuristic',
                            'exit_code': run_report.exit_code,
                            'timestamp': run_report.timestamp,
                            'example_success_history': False,
                            'decision_rationale': 'crash_without_history'
                        }
                    )
        
        if run_report.coverage < target_coverage:
            if skip_tests:
                # When tests are skipped but coverage is low, consider workflow complete
                # since we can't improve coverage without running tests
                return SyncDecision(
                    operation='all_synced',
                    reason=f'Coverage {run_report.coverage:.1f}% below target {target_coverage:.1f}% but tests skipped',
                    confidence=0.90,
                    estimated_cost=estimate_operation_cost('all_synced'),
                    details={
                        'decision_type': 'heuristic',
                        'current_coverage': run_report.coverage,
                        'target_coverage': target_coverage,
                        'tests_skipped': True,
                        'skip_tests': True
                    }
                )
            elif run_report.tests_failed == 0 and run_report.tests_passed > 0:
                # Tests pass but coverage is below target
                # CRITICAL: First check if test file actually exists
                # The run_report may have synthetic tests_passed=1 from crash/verify success
                # but actual test file hasn't been generated yet
                pdd_files = get_pdd_file_paths(basename, language, prompts_dir, context_override=context_override)
                test_file_exists = pdd_files.get('test') and pdd_files['test'].exists()

                # For non-Python languages (including TypeScript), the agentic test generator may create
                # test files with different extensions or at different paths. We need to differentiate:
                # 1. Synthetic run_report from crash/verify (test_hash=None) - tests NOT generated yet
                # 2. Real run_report from agentic test generation (test_hash set) - tests were generated
                # Only skip test generation if we have evidence that tests were actually generated.
                lang_lower = language.lower()
                is_agentic_language = lang_lower != 'python'

                # Check if this is a synthetic run report (from crash/verify) vs real test execution
                # Synthetic reports have test_hash=None because no actual test file was involved
                has_real_test_hash = run_report.test_hash is not None

                code_file_exists = pdd_files.get('code') and pdd_files['code'].exists()

                if not code_file_exists:
                    # Code file missing — can't run tests or generate tests without it.
                    # Immediately return 'generate' to regenerate from prompt.
                    return SyncDecision(
                        operation='generate',
                        reason='Code file missing with stale metadata - regenerate from prompt',
                        confidence=0.95,
                        estimated_cost=estimate_operation_cost('generate'),
                        details={
                            'decision_type': 'heuristic',
                            'code_file_exists': False,
                            'test_file_exists': test_file_exists,
                            'workflow_stage': 'code_missing_regenerate'
                        }
                    )

                if not test_file_exists and (not is_agentic_language or not has_real_test_hash):
                    # Test file doesn't exist and either:
                    # - Python (non-agentic): always need the file at expected path
                    # - Non-Python but no test_hash: synthetic run_report, tests not generated yet
                    return SyncDecision(
                        operation='test',
                        reason='Example validated but test file missing - generate tests',
                        confidence=0.90,
                        estimated_cost=estimate_operation_cost('test'),
                        details={
                            'decision_type': 'heuristic',
                            'run_report_tests_passed': run_report.tests_passed,
                            'test_file_exists': False,
                            'has_real_test_hash': has_real_test_hash,
                            'workflow_stage': 'test_generation_needed'
                        }
                    )

                # PR auto-heal scope guard (#1403): when test_extend is disabled,
                # accept the coverage gap as complete for ALL languages (incl.
                # Python) instead of escalating into coverage-driven test_extend.
                # This single branch covers both the in-process detection call
                # and the `pdd sync` subprocess that re-derives the same decision.
                if is_test_extend_disabled():
                    return SyncDecision(
                        operation='all_synced',
                        reason=f'Tests pass ({run_report.tests_passed} passed). Coverage {run_report.coverage:.1f}% below target but test_extend disabled (PDD_DISABLE_TEST_EXTEND / PR auto-heal scope guard) - accepting as complete',
                        confidence=0.90,
                        estimated_cost=estimate_operation_cost('all_synced'),
                        details={
                            'decision_type': 'heuristic',
                            'current_coverage': run_report.coverage,
                            'target_coverage': target_coverage,
                            'tests_passed': run_report.tests_passed,
                            'tests_failed': run_report.tests_failed,
                            'test_extend_skipped': True,
                            'language': language,
                            'skip_reason': 'PDD_DISABLE_TEST_EXTEND'
                        }
                    )

                # Skip test_extend for non-Python languages - code coverage tooling is Python-specific
                # and test_extend would produce no content or fail for other languages
                if language.lower() != 'python':
                    return SyncDecision(
                        operation='all_synced',
                        reason=f'Tests pass ({run_report.tests_passed} passed). Coverage {run_report.coverage:.1f}% below target but test_extend not supported for {language} - accepting as complete',
                        confidence=0.90,
                        estimated_cost=estimate_operation_cost('all_synced'),
                        details={
                            'decision_type': 'heuristic',
                            'current_coverage': run_report.coverage,
                            'target_coverage': target_coverage,
                            'tests_passed': run_report.tests_passed,
                            'tests_failed': run_report.tests_failed,
                            'test_extend_skipped': True,
                            'language': language,
                            'skip_reason': 'non-python language'
                        }
                    )
                # Return 'test_extend' to signal we need to ADD more tests, not regenerate
                return SyncDecision(
                    operation='test_extend',
                    reason=f'Tests pass ({run_report.tests_passed} passed) but coverage {run_report.coverage:.1f}% below target {target_coverage:.1f}% - extending tests',
                    confidence=0.85,
                    estimated_cost=estimate_operation_cost('test'),
                    details={
                        'decision_type': 'heuristic',
                        'current_coverage': run_report.coverage,
                        'target_coverage': target_coverage,
                        'tests_passed': run_report.tests_passed,
                        'tests_failed': run_report.tests_failed,
                        'extend_tests': True
                    }
                )
            else:
                # Bug fix: If tests_passed=0 AND tests_failed=0 AND exit_code=0,
                # the test output couldn't be parsed but tests likely passed.
                # For non-Python languages, this is common when the test framework
                # output doesn't match our parsing patterns.
                # In this case, accept the workflow as complete rather than loop infinitely.
                if run_report.tests_passed == 0 and run_report.tests_failed == 0 and run_report.exit_code == 0:
                    return SyncDecision(
                        operation='all_synced',
                        reason=f'Tests completed (exit_code=0) but coverage {run_report.coverage:.1f}% could not be verified - accepting as complete',
                        confidence=0.70,
                        estimated_cost=estimate_operation_cost('all_synced'),
                        details={
                            'decision_type': 'heuristic',
                            'current_coverage': run_report.coverage,
                            'target_coverage': target_coverage,
                            'tests_passed': run_report.tests_passed,
                            'tests_failed': run_report.tests_failed,
                            'exit_code': run_report.exit_code,
                            'unparseable_output': True
                        }
                    )
                return SyncDecision(
                    operation='test',
                    reason=f'Coverage {run_report.coverage:.1f}% below target {target_coverage:.1f}%',
                    confidence=0.85,
                    estimated_cost=estimate_operation_cost('test'),
                    details={
                        'decision_type': 'heuristic',
                        'current_coverage': run_report.coverage,
                        'target_coverage': target_coverage,
                        'tests_passed': run_report.tests_passed,
                        'tests_failed': run_report.tests_failed
                    }
                )
    
    # 2. Analyze File State
    paths = get_pdd_file_paths(basename, language, prompts_dir, context_override=context_override)
    # Issue #522: Pass stored include deps so prompt hash accounts for dependency changes
    stored_deps = fingerprint.include_deps if fingerprint else None
    current_hashes = calculate_current_hashes(paths, stored_include_deps=stored_deps)
    
    # 3. Implement the Decision Tree
    if not fingerprint:
        # No Fingerprint (New or Untracked Unit)
        if paths['prompt'].exists():
            prompt_content = paths['prompt'].read_text(encoding='utf-8', errors='ignore')
            if check_for_dependencies(prompt_content):
                return SyncDecision(
                    operation='auto-deps',
                    reason='New prompt with dependencies detected',
                    confidence=0.80,
                    estimated_cost=estimate_operation_cost('auto-deps'),
                    details={
                        'decision_type': 'heuristic',
                        'prompt_path': str(paths['prompt']),
                        'fingerprint_found': False,
                        'has_dependencies': True
                    }
                )
            else:
                return SyncDecision(
                    operation='generate',
                    reason='New prompt ready for code generation',
                    confidence=0.90,
                    estimated_cost=estimate_operation_cost('generate'),
                    details={
                        'decision_type': 'heuristic',
                        'prompt_path': str(paths['prompt']),
                        'fingerprint_found': False,
                        'has_dependencies': False
                    }
                )
        else:
            return SyncDecision(
                operation='nothing',
                reason='No prompt file and no history - nothing to do',
                confidence=1.0,
                estimated_cost=estimate_operation_cost('nothing'),
                details={
                    'decision_type': 'heuristic',
                    'prompt_exists': False,
                    'fingerprint_found': False
                }
            )
    
    # CRITICAL FIX: Validate expected files exist before hash comparison
    if fingerprint:
        file_validation = validate_expected_files(fingerprint, paths)
        missing_expected_files = [
            file_type for file_type, exists in file_validation.items() 
            if not exists
        ]
        
        if missing_expected_files:
            # Files are missing that should exist - need to regenerate
            # This prevents the incorrect analyze_conflict decision
            return _handle_missing_expected_files(
                missing_expected_files, paths, fingerprint, basename, language, prompts_dir, skip_tests, skip_verify, isolated_replay_or_repair
            )
    
    # Compare hashes only for files that actually exist (prevents None != "hash" false positives)
    changes = []
    if fingerprint:
        changes = _changed_artifacts_from_hashes(fingerprint, paths, current_hashes)
    
    if not changes:
        # No Changes (Hashes Match Fingerprint) - Progress workflow with skip awareness
        if _is_workflow_complete(paths, skip_tests, skip_verify, basename, language):
            return SyncDecision(
                operation='nothing',
                reason=f'All required files synchronized (skip_tests={skip_tests}, skip_verify={skip_verify})',
                confidence=1.0,
                estimated_cost=estimate_operation_cost('nothing'),
                details={
                    'decision_type': 'heuristic',
                    'skip_tests': skip_tests,
                    'skip_verify': skip_verify,
                    'workflow_complete': True
                }
            )

        # Handle incomplete workflow when all files exist (including test)
        # This addresses the blind spot where crash/verify/test logic only runs when test is missing
        if (paths['code'].exists() and paths['example'].exists() and paths['test'].exists()):
            run_report = read_run_report(basename, language, paths=paths)

            # BUG 4 & 1: No run_report OR crash detected (exit_code != 0)
            if not run_report or run_report.exit_code != 0:
                # Bug #349: If tests passed, ignore non-zero exit code
                tests_passed_successfully = run_report and run_report.tests_passed > 0 and run_report.tests_failed == 0
                
                if not tests_passed_successfully:
                    return SyncDecision(
                        operation='crash',
                        reason='All files exist but needs validation' +
                               (' - no run_report' if not run_report else f' - exit_code={run_report.exit_code}'),
                        confidence=0.85,
                        estimated_cost=estimate_operation_cost('crash'),
                        details={
                            'decision_type': 'heuristic',
                            'all_files_exist': True,
                            'run_report_missing': not run_report,
                            'exit_code': None if not run_report else run_report.exit_code,
                            'workflow_stage': 'post_regeneration_validation'
                        }
                    )

            # BUG 2: Verify not run yet (run_report exists, exit_code=0, but command != verify/test)
            if fingerprint and fingerprint.command not in ['verify', 'test', 'fix', 'update'] and not skip_verify:
                return SyncDecision(
                    operation='verify',
                    reason='All files exist but verification not completed',
                    confidence=0.85,
                    estimated_cost=estimate_operation_cost('verify'),
                    details={
                        'decision_type': 'heuristic',
                        'all_files_exist': True,
                        'last_command': fingerprint.command,
                        'workflow_stage': 'verification_pending'
                    }
                )

            # Stale run_report detected: _is_workflow_complete returned False but all other conditions passed
            # This happens when run_report.test_hash doesn't match current test file, or
            # when fingerprint timestamp > run_report timestamp (legacy detection)
            # Need to re-run tests to get accurate results
            # Bug #349: Also check if tests passed successfully even if exit_code != 0
            is_success = run_report and ((run_report.exit_code == 0) or (run_report.tests_passed > 0 and run_report.tests_failed == 0))
            
            if is_success:
                return SyncDecision(
                    operation='test',
                    reason='Run report is stale - need to re-run tests to verify current state',
                    confidence=0.9,
                    estimated_cost=estimate_operation_cost('test'),
                    details={
                        'decision_type': 'heuristic',
                        'all_files_exist': True,
                        'run_report_stale': True,
                        'run_report_test_hash': run_report.test_hash,
                        'workflow_stage': 'revalidation'
                    }
                )

        # Progress workflow considering skip flags
        if paths['code'].exists() and not paths['example'].exists():
            return SyncDecision(
                operation='example',
                reason='Code exists but example missing - progress workflow',
                confidence=0.85,
                estimated_cost=estimate_operation_cost('example'),
                details={
                    'decision_type': 'heuristic',
                    'code_path': str(paths['code']),
                    'code_exists': True,
                    'example_exists': False
                }
            )
        
        if (paths['code'].exists() and paths['example'].exists() and
            not skip_tests and not paths['test'].exists()):

            # Check if example has been crash-tested and verified before allowing test generation
            run_report = read_run_report(basename, language, paths=paths)

            # For non-Python languages (including TypeScript), the agentic test generator may create
            # test files with different extensions or at different paths. If the run_report
            # shows tests passed successfully AND has a test_hash (not synthetic), consider complete.
            # Synthetic run_reports from crash/verify have test_hash=None and should NOT skip test generation.
            lang_lower = language.lower()
            is_agentic_language = lang_lower != 'python'
            has_real_test_hash = run_report.test_hash is not None if run_report else False
            if is_agentic_language and run_report and run_report.tests_passed > 0 and run_report.tests_failed == 0 and has_real_test_hash:
                return SyncDecision(
                    operation='all_synced',
                    reason=f'Tests pass ({run_report.tests_passed} passed) via agentic test generation - workflow complete',
                    confidence=0.90,
                    estimated_cost=estimate_operation_cost('all_synced'),
                    details={
                        'decision_type': 'heuristic',
                        'tests_passed': run_report.tests_passed,
                        'tests_failed': run_report.tests_failed,
                        'language': language,
                        'agentic_test_complete': True,
                        'test_hash': run_report.test_hash
                    }
                )

            if not run_report and not skip_verify:
                # No run report exists - need to test the example first
                # But if skip_verify is True, skip crash/verify and go to test generation
                return SyncDecision(
                    operation='crash',
                    reason='Example exists but needs runtime testing before test generation',
                    confidence=0.85,
                    estimated_cost=estimate_operation_cost('crash'),
                    details={
                        'decision_type': 'heuristic',
                        'code_path': str(paths['code']),
                        'example_path': str(paths['example']),
                        'no_run_report': True,
                        'workflow_stage': 'crash_validation'
                    }
                )
            elif run_report and run_report.exit_code != 0 and not skip_verify:
                # Example crashed - fix it before proceeding
                # But if skip_verify is True, skip crash fix and proceed
                return SyncDecision(
                    operation='crash',
                    reason='Example crashes - fix runtime errors before test generation',
                    confidence=0.90,
                    estimated_cost=estimate_operation_cost('crash'),
                    details={
                        'decision_type': 'heuristic',
                        'exit_code': run_report.exit_code,
                        'workflow_stage': 'crash_fix'
                    }
                )
            elif fingerprint and fingerprint.command != 'verify' and not skip_verify:
                # Example runs but hasn't been verified yet
                return SyncDecision(
                    operation='verify',
                    reason='Example runs but needs verification before test generation',
                    confidence=0.85,
                    estimated_cost=estimate_operation_cost('verify'),
                    details={
                        'decision_type': 'heuristic',
                        'exit_code': run_report.exit_code,
                        'last_command': fingerprint.command,
                        'workflow_stage': 'verify_validation'
                    }
                )
            else:
                # Example runs and is verified (or verify is skipped) - now safe to generate tests
                return SyncDecision(
                    operation='test',
                    reason='Example validated - ready for test generation',
                    confidence=0.85,
                    estimated_cost=estimate_operation_cost('test'),
                    details={
                        'decision_type': 'heuristic',
                        'code_path': str(paths['code']),
                        'example_path': str(paths['example']),
                        'code_exists': True,
                        'example_exists': True,
                        'test_exists': False,
                        'workflow_stage': 'test_generation'
                    }
                )
        
        # Some files are missing but no changes detected
        if not paths['code'].exists():
            if paths['prompt'].exists():
                # CRITICAL FIX: Check if auto-deps was just completed to prevent infinite loop
                if fingerprint and fingerprint.command == 'auto-deps':
                    return SyncDecision(
                        operation='generate',
                        reason='Auto-deps completed, now generate missing code file',
                        confidence=0.90,
                        estimated_cost=estimate_operation_cost('generate'),
                        details={
                            'decision_type': 'heuristic',
                            'prompt_path': str(paths['prompt']),
                            'code_exists': False,
                            'auto_deps_completed': True,
                            'previous_command': fingerprint.command
                        }
                    )
                
                prompt_content = paths['prompt'].read_text(encoding='utf-8', errors='ignore')
                if check_for_dependencies(prompt_content):
                    return SyncDecision(
                        operation='auto-deps',
                        reason='Missing code file, prompt has dependencies',
                        confidence=0.80,
                        estimated_cost=estimate_operation_cost('auto-deps'),
                        details={
                            'decision_type': 'heuristic',
                            'prompt_path': str(paths['prompt']),
                            'code_exists': False,
                            'has_dependencies': True
                        }
                    )
                else:
                    return SyncDecision(
                        operation='generate',
                        reason='Missing code file - generate from prompt',
                        confidence=0.90,
                        estimated_cost=estimate_operation_cost('generate'),
                        details={
                            'decision_type': 'heuristic',
                            'prompt_path': str(paths['prompt']),
                            'code_exists': False,
                            'has_dependencies': False
                        }
                    )
    
    elif len(changes) == 1:
        # Simple Changes (Single File Modified)
        change = changes[0]
        
        if change == 'prompt':
            prompt_content = paths['prompt'].read_text(encoding='utf-8', errors='ignore')
            if check_for_dependencies(prompt_content):
                return SyncDecision(
                    operation='auto-deps',
                    reason='Prompt changed and dependencies need updating',
                    confidence=0.85,
                    estimated_cost=estimate_operation_cost('auto-deps'),
                    details={
                        'decision_type': 'heuristic',
                        'changed_file': 'prompt',
                        'has_dependencies': True,
                        'prompt_changed': True
                    }
                )
            else:
                return SyncDecision(
                    operation='generate',
                    reason='Prompt changed - regenerate code',
                    confidence=0.90,
                    estimated_cost=estimate_operation_cost('generate'),
                    details={
                        'decision_type': 'heuristic',
                        'changed_file': 'prompt',
                        'has_dependencies': False,
                        'prompt_changed': True
                    }
                )
        
        elif change == 'code':
            return SyncDecision(
                operation='update',
                reason='Code changed - update prompt to reflect changes',
                confidence=0.85,
                estimated_cost=estimate_operation_cost('update'),
                details={
                    'decision_type': 'heuristic',
                    'changed_file': 'code',
                    'code_changed': True
                }
            )
        
        elif change == 'test':
            return SyncDecision(
                operation='test',
                reason='Test changed - run new tests',
                confidence=0.80,
                estimated_cost=estimate_operation_cost('test'),
                details={
                    'decision_type': 'heuristic',
                    'changed_file': 'test',
                    'test_changed': True
                }
            )
        
        elif change == 'example':
            return SyncDecision(
                operation='verify',
                reason='Example changed - verify new example',
                confidence=0.80,
                estimated_cost=estimate_operation_cost('verify'),
                details={
                    'decision_type': 'heuristic',
                    'changed_file': 'example',
                    'example_changed': True
                }
            )
    
    else:
        # Complex Changes (Multiple Files Modified)
        # CRITICAL: Only treat as conflict if prompt changed along with derived artifacts
        # If only derived artifacts changed (code, example, test), this is NOT a conflict
        # per PDD doctrine - all are derived from the unchanged prompt

        if 'prompt' in changes:
            return _prompt_derived_conflict_decision(
                basename=basename,
                language=language,
                changes=changes,
                paths=paths,
                fingerprint=fingerprint,
                read_only=read_only,
            )
        else:
            # Only derived artifacts changed - prompt (source of truth) is unchanged
            # Continue workflow from where it was interrupted

            # If code changed, need to re-verify
            if 'code' in changes:
                return SyncDecision(
                    operation='verify',
                    reason='Derived files changed (prompt unchanged) - verify code works',
                    confidence=0.85,
                    estimated_cost=estimate_operation_cost('verify'),
                    details={
                        'decision_type': 'heuristic',
                        'changed_files': changes,
                        'num_changes': len(changes),
                        'prompt_changed': False,
                        'workflow_stage': 'continue_after_interruption'
                    }
                )
            # If only example/test changed
            elif 'example' in changes:
                return SyncDecision(
                    operation='verify',
                    reason='Example changed (prompt unchanged) - verify example runs',
                    confidence=0.85,
                    estimated_cost=estimate_operation_cost('verify'),
                    details={
                        'decision_type': 'heuristic',
                        'changed_files': changes,
                        'prompt_changed': False
                    }
                )
            elif 'test' in changes:
                return SyncDecision(
                    operation='test',
                    reason='Test changed (prompt unchanged) - run tests',
                    confidence=0.85,
                    estimated_cost=estimate_operation_cost('test'),
                    details={
                        'decision_type': 'heuristic',
                        'changed_files': changes,
                        'prompt_changed': False
                    }
                )
    
    # Fallback - should not reach here normally
    return SyncDecision(
        operation='nothing',
        reason='No clear operation determined',
        confidence=0.50,
        estimated_cost=estimate_operation_cost('nothing'),
        details={
            'decision_type': 'heuristic',
            'fingerprint_exists': fingerprint is not None,
            'changes': changes,
            'fallback': True
        }
    )


def analyze_conflict_with_llm(
    basename: str,
    language: str,
    fingerprint: Fingerprint,
    changed_files: List[str],
    prompts_dir: str = "prompts",
    context_override: Optional[str] = None,
) -> SyncDecision:
    """
    Resolve complex sync conflicts using an LLM.
    
    Args:
        basename: The base name for the PDD unit
        language: The programming language
        fingerprint: The last known good state
        changed_files: List of files that have changed
        prompts_dir: Directory containing prompt files
    
    Returns:
        SyncDecision object with LLM-recommended operation
    """
    
    try:
        # 1. Load LLM Prompt
        prompt_template = load_prompt_template("sync_analysis_LLM")
        if not prompt_template:
            # Fallback if template not found
            return SyncDecision(
                operation='fail_and_request_manual_merge',
                reason='LLM analysis template not found - manual merge required',
                confidence=0.0,
                estimated_cost=estimate_operation_cost('fail_and_request_manual_merge'),
                details={
                    'decision_type': 'llm',
                    'error': 'Template not available',
                    'changed_files': changed_files
                }
            )
        
        # 2. Gather file paths and diffs
        paths = get_pdd_file_paths(basename, language, prompts_dir, context_override=context_override)
        
        # Generate diffs for changed files
        # Escape braces in diffs to prevent .format() from interpreting
        # code content like {uid} as template placeholders
        def _escape_braces(s: str) -> str:
            return s.replace("{", "{{").replace("}", "}}")

        diffs = {}
        for file_type in changed_files:
            if file_type in paths and paths[file_type].exists():
                diffs[f"{file_type}_diff"] = _escape_braces(get_git_diff(paths[file_type]))
                diffs[f"{file_type}_path"] = str(paths[file_type])
            else:
                diffs[f"{file_type}_diff"] = ""
                diffs[f"{file_type}_path"] = str(paths.get(file_type, ''))
        
        # 3. Format the prompt
        formatted_prompt = prompt_template.format(
            fingerprint=json.dumps({
                'pdd_version': fingerprint.pdd_version,
                'timestamp': fingerprint.timestamp,
                'command': fingerprint.command,
                'prompt_hash': fingerprint.prompt_hash,
                'code_hash': fingerprint.code_hash,
                'example_hash': fingerprint.example_hash,
                'test_hash': fingerprint.test_hash
            }, indent=2),
            changed_files_list=', '.join(changed_files),
            prompt_diff=diffs.get('prompt_diff', ''),
            code_diff=diffs.get('code_diff', ''),
            example_diff=diffs.get('example_diff', ''),
            test_diff=diffs.get('test_diff', ''),
            prompt_path=diffs.get('prompt_path', ''),
            code_path=diffs.get('code_path', ''),
            example_path=diffs.get('example_path', ''),
            test_path=diffs.get('test_path', '')
        )
        
        # 4. Invoke LLM with caching for determinism
        response = llm_invoke(
            prompt=formatted_prompt,
            input_json={},
            strength=0.7,  # Use a consistent strength for determinism
            temperature=0.0,  # Use temperature 0 for deterministic output
            verbose=False
        )
        
        # 5. Parse and validate response
        try:
            llm_result = json.loads(response['result'])
            
            # Validate required keys
            required_keys = ['next_operation', 'reason', 'confidence']
            if not all(key in llm_result for key in required_keys):
                raise ValueError("Missing required keys in LLM response")
            
            # Check confidence threshold
            confidence = float(llm_result.get('confidence', 0.0))
            if confidence < 0.75:
                return SyncDecision(
                    operation='fail_and_request_manual_merge',
                    reason=f'LLM confidence too low ({confidence:.2f}) - manual merge required',
                    confidence=confidence,
                    estimated_cost=response.get('cost', 0.0),
                    details={
                        'decision_type': 'llm',
                        'llm_response': llm_result,
                        'changed_files': changed_files,
                        'confidence_threshold': 0.75
                    }
                )
            
            # Extract operation and details
            operation = llm_result['next_operation']
            reason = llm_result['reason']
            merge_strategy = llm_result.get('merge_strategy', {})
            follow_up_operations = llm_result.get('follow_up_operations', [])
            
            return SyncDecision(
                operation=operation,
                reason=f"LLM analysis: {reason}",
                confidence=confidence,
                estimated_cost=response.get('cost', 0.0),
                details={
                    'decision_type': 'llm',
                    'llm_response': llm_result,
                    'changed_files': changed_files,
                    'merge_strategy': merge_strategy,
                    'follow_up_operations': follow_up_operations
                },
                prerequisites=follow_up_operations
            )
            
        except (json.JSONDecodeError, ValueError, KeyError) as e:
            # Invalid LLM response - fallback to manual merge
            return SyncDecision(
                operation='fail_and_request_manual_merge',
                reason=f'Invalid LLM response: {e} - manual merge required',
                confidence=0.0,
                estimated_cost=response.get('cost', 0.0),
                details={
                    'decision_type': 'llm',
                    'error': str(e),
                    'raw_response': response.get('result', ''),
                    'changed_files': changed_files,
                    'llm_error': True
                }
            )
    
    except Exception as e:
        # Any other error - fallback to manual merge
        return SyncDecision(
            operation='fail_and_request_manual_merge',
            reason=f'Error during LLM analysis: {e} - manual merge required',
            confidence=0.0,
            estimated_cost=estimate_operation_cost('fail_and_request_manual_merge'),
            details={
                'decision_type': 'llm',
                'error': str(e),
                'changed_files': changed_files,
                'llm_error': True
            }
        )


if __name__ == "__main__":
    # Example usage
    if len(sys.argv) < 3 or len(sys.argv) > 4:
        print("Usage: python sync_determine_operation.py <basename> <language> [target_coverage]")
        sys.exit(1)
    
    basename = sys.argv[1]
    language = sys.argv[2]
    target_coverage = float(sys.argv[3]) if len(sys.argv) == 4 else 90.0
    
    decision = sync_determine_operation(basename, language, target_coverage)
    
    print(f"Operation: {decision.operation}")
    print(f"Reason: {decision.reason}")
    print(f"Estimated Cost: ${decision.estimated_cost:.2f}")
    print(f"Confidence: {decision.confidence:.2f}")
    if decision.details:
        print(f"Details: {json.dumps(decision.details, indent=2)}")
