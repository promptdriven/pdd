"""Finalize PDD fingerprints at CLI-created PR boundaries."""

from __future__ import annotations

import os
import subprocess
import threading
from contextlib import contextmanager
from dataclasses import dataclass
from pathlib import Path
from typing import Dict, Iterable, Iterator, List, Optional, Sequence, Set, Tuple

from .architecture_registry import find_architecture_for_project
from .git_porcelain import iter_changed_paths, parse_porcelain_z
from .metadata_sync import run_metadata_sync
from .operation_log import (
    get_fingerprint_path,
    get_run_report_path,
    infer_module_identity,
    save_fingerprint,
)
from .sync_determine_operation import (
    calculate_current_hashes,
    get_pdd_file_paths,
    read_fingerprint,
)


_FINALIZE_LOCK = threading.Lock()
_EXCLUDED_PARTS = {
    ".git",
    ".pdd",
    ".venv",
    "venv",
    "env",
    "__pycache__",
    "node_modules",
    ".pytest_cache",
    ".mypy_cache",
    ".ruff_cache",
    ".tox",
    ".nox",
    "dist",
    "build",
}


def _strip_current_dir_prefix(path: str) -> str:
    normalized = path.replace("\\", "/")
    while normalized.startswith("./"):
        normalized = normalized[2:]
    return normalized


@dataclass(frozen=True)
class FinalizedFingerprint:
    """Fingerprint written for one PDD module."""

    basename: str
    language: str
    prompt_path: Path
    metadata_path: Path

    @property
    def metadata_relpath(self) -> str:
        """Return the repo-relative metadata path as POSIX text."""
        return self.metadata_path.as_posix()


@dataclass(frozen=True)
class PRMetadataFinalizationResult:
    """Result for PR-boundary metadata finalization."""

    ok: bool
    finalized: Tuple[FinalizedFingerprint, ...] = ()
    touched_modules: Tuple[str, ...] = ()
    message: str = ""

    @property
    def metadata_paths(self) -> Tuple[str, ...]:
        """Return repo-relative metadata paths in finalization order."""
        return tuple(item.metadata_relpath for item in self.finalized)


@dataclass
class _ModuleInfo:
    basename: str
    language: str
    prompt_path: Path
    paths: Dict[str, object]
    relpaths: Set[str]


@contextmanager
def _pushd(path: Path) -> Iterator[None]:
    previous = Path.cwd()
    os.chdir(path)
    try:
        yield
    finally:
        os.chdir(previous)


def is_pdd_meta_artifact(path: str) -> bool:
    """Return True for operation-log files under ``.pdd/meta``."""
    normalized = _strip_current_dir_prefix(path)
    return normalized.startswith(".pdd/meta/")


def _repo_rel(path: Path, repo_root: Path) -> str:
    try:
        return path.resolve().relative_to(repo_root.resolve()).as_posix()
    except (OSError, ValueError):
        return _strip_current_dir_prefix(path.as_posix())


def _as_abs(path_like: object, repo_root: Path) -> Optional[Path]:
    if not isinstance(path_like, Path):
        return None
    return path_like if path_like.is_absolute() else repo_root / path_like


def _normalize_changed_path(path: str, repo_root: Path) -> str:
    raw = Path(path)
    if raw.is_absolute():
        return _repo_rel(raw, repo_root)
    return _strip_current_dir_prefix(raw.as_posix())


def _git_changed_paths(repo_root: Path) -> List[str]:
    result = subprocess.run(
        ["git", "status", "--porcelain=v1", "-z", "--untracked-files=all"],
        cwd=repo_root,
        capture_output=True,
        check=False,
    )
    if result.returncode != 0:
        return []
    return list(iter_changed_paths(parse_porcelain_z(result.stdout)))


def _prompt_roots(repo_root: Path) -> List[Path]:
    primary_roots = _valid_prompt_roots(
        repo_root,
        [repo_root / "prompts", repo_root / "pdd" / "prompts"],
    )
    if primary_roots:
        return primary_roots
    return _valid_prompt_roots(repo_root, repo_root.rglob("prompts"))


def _valid_prompt_roots(repo_root: Path, candidates: Iterable[Path]) -> List[Path]:
    roots: List[Path] = []
    seen: Set[Path] = set()
    for candidate in candidates:
        try:
            rel_parts = candidate.relative_to(repo_root).parts
            if any(part in _EXCLUDED_PARTS for part in rel_parts):
                continue
            resolved = candidate.resolve()
        except (OSError, ValueError):
            continue
        if not resolved.is_dir() or resolved in seen:
            continue
        seen.add(resolved)
        roots.append(resolved)
    return roots


def _prompt_scan_candidates(repo_root: Path) -> Iterator[Path]:
    roots = _prompt_roots(repo_root) or [repo_root]
    for root in roots:
        for prompt_path in root.rglob("*.prompt"):
            try:
                rel_parts = prompt_path.relative_to(repo_root).parts
            except ValueError:
                rel_parts = prompt_path.parts
            if any(part in _EXCLUDED_PARTS for part in rel_parts):
                continue
            if prompt_path.is_file():
                yield prompt_path


def _nearest_prompts_dir(prompt_path: Path) -> str:
    resolved = prompt_path.resolve()
    for parent in resolved.parents:
        if parent.name == "prompts":
            return parent.as_posix()
    return prompt_path.parent.as_posix()


def _module_paths(
    basename: str,
    language: str,
    prompt_path: Path,
    repo_root: Path,
) -> Dict[str, object]:
    try:
        paths = get_pdd_file_paths(
            basename,
            language,
            prompts_dir=_nearest_prompts_dir(prompt_path),
        )
    except Exception:  # pylint: disable=broad-exception-caught
        paths = {"prompt": prompt_path}
    paths["prompt"] = prompt_path

    normalized: Dict[str, object] = {}
    for key, value in paths.items():
        if key == "test_files" and isinstance(value, list):
            normalized[key] = [
                p if p.is_absolute() else repo_root / p
                for p in value
                if isinstance(p, Path)
            ]
        elif isinstance(value, Path):
            normalized[key] = value if value.is_absolute() else repo_root / value
    return normalized


def _relpaths_for_paths(paths: Dict[str, object], repo_root: Path) -> Set[str]:
    relpaths: Set[str] = set()
    for key, value in paths.items():
        if key == "test_files" and isinstance(value, list):
            for item in value:
                if isinstance(item, Path):
                    relpaths.add(_repo_rel(item, repo_root))
        elif isinstance(value, Path):
            relpaths.add(_repo_rel(value, repo_root))
    return relpaths


def _discover_modules(repo_root: Path) -> List[_ModuleInfo]:
    modules: List[_ModuleInfo] = []
    seen: Set[Tuple[str, str, str]] = set()
    for prompt_path in _prompt_scan_candidates(repo_root):
        basename, language = infer_module_identity(prompt_path)
        if not basename or not language:
            continue
        paths = _module_paths(basename, language, prompt_path, repo_root)
        key = (basename, language, _repo_rel(prompt_path, repo_root))
        if key in seen:
            continue
        seen.add(key)
        modules.append(
            _ModuleInfo(
                basename=basename,
                language=language,
                prompt_path=prompt_path,
                paths=paths,
                relpaths=_relpaths_for_paths(paths, repo_root),
            )
        )
    modules.sort(key=lambda item: (item.basename, item.language))
    return modules


def _changed_modules(
    repo_root: Path,
    changed_paths: Sequence[str],
) -> List[_ModuleInfo]:
    changed = {
        _normalize_changed_path(path, repo_root)
        for path in changed_paths
        if path and not is_pdd_meta_artifact(path)
    }
    if not changed:
        return []
    modules = []
    for module in _discover_modules(repo_root):
        if module.relpaths.intersection(changed):
            modules.append(module)
    return modules


def _preserved_command(basename: str, language: str) -> str:
    previous = read_fingerprint(basename, language)
    previous_command = getattr(previous, "command", None) if previous else None
    if previous_command in {"verify", "test", "fix", "update"}:
        return str(previous_command)
    return "fix"


def _verify_fingerprint_fresh(module: _ModuleInfo) -> Optional[str]:
    fingerprint = read_fingerprint(module.basename, module.language)
    if fingerprint is None:
        return "fingerprint missing after save"

    current = calculate_current_hashes(
        module.paths,
        stored_include_deps=fingerprint.include_deps,
    )
    checks = {
        "prompt_hash": fingerprint.prompt_hash,
        "code_hash": fingerprint.code_hash,
        "example_hash": fingerprint.example_hash,
        "test_hash": fingerprint.test_hash,
        "test_files": fingerprint.test_files,
    }
    for field, actual in checks.items():
        if field in current and current[field] != actual:
            return f"{field} is stale"
    return None


def _metadata_relpath(basename: str, language: str, repo_root: Path) -> Path:
    path = get_fingerprint_path(basename, language)
    absolute = path if path.is_absolute() else repo_root / path
    return Path(_repo_rel(absolute, repo_root))


def _run_report_path(basename: str, language: str, repo_root: Path) -> Path:
    path = get_run_report_path(basename, language)
    return path if path.is_absolute() else repo_root / path


def _restore_run_report(path: Path, contents: Optional[bytes]) -> None:
    if contents is None or path.exists():
        return
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_bytes(contents)


def _stage_fingerprint(repo_root: Path, relpath: Path) -> Optional[str]:
    result = subprocess.run(
        ["git", "add", "-f", "--", relpath.as_posix()],
        cwd=repo_root,
        capture_output=True,
        text=True,
        check=False,
    )
    if result.returncode == 0:
        return None
    return result.stderr.strip() or result.stdout.strip() or "git add failed"


def stage_paths_scoped(
    repo_root: Path,
    paths: Iterable[str],
    *,
    force: bool = False,
    exclude_pdd_meta: bool = True,
) -> Tuple[bool, str]:
    """Stage exact pathspecs, optionally excluding arbitrary ``.pdd/meta`` paths."""
    for path in paths:
        normalized = _normalize_changed_path(path, repo_root)
        if not normalized:
            continue
        if exclude_pdd_meta and is_pdd_meta_artifact(normalized):
            continue
        cmd = ["git", "add"]
        if force:
            cmd.append("-f")
        if normalized.startswith("-"):
            cmd.extend(["--", normalized])
        else:
            cmd.append(normalized)
        result = subprocess.run(
            cmd,
            cwd=repo_root,
            capture_output=True,
            text=True,
            check=False,
        )
        if result.returncode != 0:
            detail = result.stderr.strip() or result.stdout.strip()
            return False, f"Failed to stage {normalized}: {detail}"
    return True, ""


def finalize_pr_metadata(  # pylint: disable=too-many-locals
    repo_root: Path,
    changed_paths: Optional[Iterable[str]] = None,
    *,
    stage: bool = True,
) -> PRMetadataFinalizationResult:
    """Finalize fingerprints for PDD modules touched by a pending PR update."""
    repo_root = Path(repo_root).resolve()
    raw_changed = (
        list(changed_paths)
        if changed_paths is not None
        else _git_changed_paths(repo_root)
    )

    with _FINALIZE_LOCK:
        with _pushd(repo_root):
            modules = _changed_modules(repo_root, raw_changed)
            if not modules:
                return PRMetadataFinalizationResult(
                    ok=True,
                    message="No PDD-owned changes detected.",
                )

            arch_candidates = find_architecture_for_project(repo_root)
            architecture_path = arch_candidates[0] if arch_candidates else None

            finalized: List[FinalizedFingerprint] = []
            for module in modules:
                code_path = _as_abs(module.paths.get("code"), repo_root)
                run_report_path = _run_report_path(
                    module.basename,
                    module.language,
                    repo_root,
                )
                run_report_contents = (
                    run_report_path.read_bytes() if run_report_path.exists() else None
                )
                try:
                    result = run_metadata_sync(
                        module.prompt_path,
                        code_path=code_path,
                        repo_root=repo_root,
                        architecture_path=architecture_path,
                    )
                except Exception as exc:  # pylint: disable=broad-exception-caught
                    return PRMetadataFinalizationResult(
                        ok=False,
                        touched_modules=tuple(m.basename for m in modules),
                        message=(
                            f"metadata finalization failed for "
                            f"{module.basename}: {exc}"
                        ),
                    )
                finally:
                    _restore_run_report(run_report_path, run_report_contents)
                if not getattr(result, "ok", False):
                    failing = getattr(result, "failing_stage", None) or "unknown"
                    return PRMetadataFinalizationResult(
                        ok=False,
                        touched_modules=tuple(m.basename for m in modules),
                        message=(
                            f"metadata finalization failed for "
                            f"{module.basename}: stage={failing}"
                        ),
                    )

                save_fingerprint(
                    basename=module.basename,
                    language=module.language,
                    operation=_preserved_command(module.basename, module.language),
                    paths=module.paths,
                    cost=0.0,
                    model="metadata_sync",
                )
                stale_reason = _verify_fingerprint_fresh(module)
                if stale_reason:
                    return PRMetadataFinalizationResult(
                        ok=False,
                        touched_modules=tuple(m.basename for m in modules),
                        message=(
                            f"metadata finalization failed for "
                            f"{module.basename}: {stale_reason}"
                        ),
                    )

                metadata_path = _metadata_relpath(module.basename, module.language, repo_root)
                if stage:
                    stage_error = _stage_fingerprint(repo_root, metadata_path)
                    if stage_error:
                        return PRMetadataFinalizationResult(
                            ok=False,
                            touched_modules=tuple(m.basename for m in modules),
                            message=(
                                "metadata staging verification failed: "
                                f"missing {metadata_path.as_posix()} ({stage_error})"
                            ),
                        )
                finalized.append(
                    FinalizedFingerprint(
                        basename=module.basename,
                        language=module.language,
                        prompt_path=module.prompt_path,
                        metadata_path=metadata_path,
                    )
                )

            return PRMetadataFinalizationResult(
                ok=True,
                finalized=tuple(finalized),
                touched_modules=tuple(module.basename for module in modules),
                message=(
                    "metadata finalized for "
                    + ", ".join(item.basename for item in finalized)
                ),
            )
